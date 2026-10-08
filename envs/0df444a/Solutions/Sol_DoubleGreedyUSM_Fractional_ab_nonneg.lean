-- Prove2me | solution 1 for DoubleGreedyUSM.Fractional.ab_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:51:21.687569+00:00
-- url     : https://prove2.me/submissions/738df36d-1ab6-46a6-8689-b8ca0179209c

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4



namespace DoubleGreedyUSM.Fractional

open NonmonotoneSubmod.Shared

section dgsec

variable {X : Type} [Fintype X] [DecidableEq X]

theorem dg_wsum (x : X → ℝ) :
    ∑ S : Finset X, ∏ i : X, (if i ∈ S then x i else 1 - x i) = 1 := by
  have h := Fintype.prod_add x (fun i => 1 - x i)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun S _ => ?_
  have := Finset.prod_piecewise (Finset.univ : Finset X) S x (fun i => 1 - x i)
  simp only [Finset.univ_inter, ← Finset.compl_eq_univ_sdiff] at this
  rw [← this]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Finset.piecewise]

theorem dg_wnn (x : X → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (S : Finset X) :
    0 ≤ ∏ i : X, (if i ∈ S then x i else 1 - x i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact h0 i
  · linarith [h1 i]

theorem dg_mono (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g h : Finset X → ℝ) (hgh : ∀ S, g S ≤ h S) : F g q ≤ F h q := by
  unfold F
  exact Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (hgh S) (dg_wnn q h0 h1 S)

theorem dg_nonpos (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (g : Finset X → ℝ) (hg : ∀ S, g S ≤ 0) : F g q ≤ 0 := by
  have hc : F (fun _ => (0:ℝ)) q = 0 := by unfold F; simp
  calc F g q ≤ F (fun _ => (0:ℝ)) q := dg_mono q h0 h1 _ _ hg
    _ = 0 := hc

theorem dg_sub (g h : Finset X → ℝ) (q : X → ℝ) :
    F (fun S => g S - h S) q = F g q - F h q := by
  unfold F
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

noncomputable def dgR (q : X → ℝ) (x : X) (T : Finset X) : ℝ :=
  ∏ i ∈ (Finset.univ.erase x), (if i ∈ T then q i else 1 - q i)

theorem dg_decomp (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q =
      ∑ T ∈ (Finset.univ.erase x).powerset,
        ((1 - q x) * g T + q x * g (insert x T)) * dgR q x T := by
  unfold F
  have hU : (Finset.univ : Finset (Finset X)) = (insert x (Finset.univ.erase x)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ x), Finset.powerset_univ]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  rw [hU, Finset.sum_powerset_insert hxn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  have h1 : ∏ i : X, (if i ∈ T then q i else 1 - q i) = (1 - q x) * dgR q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp [hxT, dgR]
  have h2 : ∏ i : X, (if i ∈ insert x T then q i else 1 - q i) = q x * dgR q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [Finset.mem_insert, true_or, if_true, dgR]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    simp [hix]
  rw [h1, h2]
  ring

theorem dg_ins (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (insert x S)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g (insert x T) * dgR q x T := by
  rw [dg_decomp]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [Finset.insert_idem]
  ring

theorem dg_erase (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F (fun S => g (S.erase x)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g T * dgR q x T := by
  rw [dg_decomp]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  rw [Finset.erase_insert hxT, Finset.erase_eq_of_notMem hxT]
  ring

theorem dg_split (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    F g q = (1 - q x) * F (fun S => g (S.erase x)) q + q x * F (fun S => g (insert x S)) q := by
  rw [dg_decomp g q x, dg_ins g q x, dg_erase g q x, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem dgR_update (q : X → ℝ) (v : X) (c : ℝ) (T : Finset X) :
    dgR (Function.update q v c) v T = dgR q v T := by
  unfold dgR
  refine Finset.prod_congr rfl fun i hi => ?_
  have hix : i ≠ v := Finset.ne_of_mem_erase hi
  simp [Function.update_of_ne hix]

theorem dg_update (g : Finset X → ℝ) (q : X → ℝ) (v : X) (c : ℝ) :
    F g (Function.update q v c) = (1 - c) * F (fun S => g (S.erase v)) q
      + c * F (fun S => g (insert v S)) q := by
  rw [dg_split g _ v, Function.update_self, dg_ins, dg_erase, dg_ins, dg_erase]
  simp only [dgR_update]

/-- marginal function -/
def dgD (g : Finset X → ℝ) (v : X) : Finset X → ℝ := fun S => g (insert v S) - g (S.erase v)

theorem dg_lin (g : Finset X → ℝ) (q : X → ℝ) (v : X) (c : ℝ) :
    F g (Function.update q v c) = F g (Function.update q v 0) + c * F (dgD g v) q := by
  rw [dg_update, dg_update]
  have := dg_sub (fun S => g (insert v S)) (fun S => g (S.erase v)) q
  unfold dgD; rw [this]; ring

theorem dg_lin' (g : Finset X → ℝ) (q : X → ℝ) (v : X) :
    F g q = F g (Function.update q v 0) + q v * F (dgD g v) q := by
  have := dg_lin g q v (q v)
  rwa [Function.update_eq_self] at this

theorem dg_anti_step (h : Finset X → ℝ) (hh : ∀ S T, S ⊆ T → h T ≤ h S)
    (q : X → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) (v : X) (c d : ℝ) (hcd : c ≤ d) :
    F h (Function.update q v d) ≤ F h (Function.update q v c) := by
  rw [dg_lin h q v d, dg_lin h q v c]
  have : F (dgD h v) q ≤ 0 := by
    apply dg_nonpos q h0 h1
    intro S
    unfold dgD
    linarith [hh (S.erase v) (insert v S) (fun y hy => Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hy))]
  nlinarith

theorem dg_anti (h : Finset X → ℝ) (hh : ∀ S T, S ⊆ T → h T ≤ h S)
    (x y : X → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) (hy1 : ∀ i, y i ≤ 1) :
    F h y ≤ F h x := by
  have key : ∀ s : Finset X, F h (fun v => if v ∈ s then y v else x v) ≤ F h x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert v s hv ih =>
      set z : X → ℝ := fun w => if w ∈ s then y w else x w with hz
      have hz0 : ∀ i, 0 ≤ z i := fun i => by
        simp only [hz]; split_ifs <;> linarith [hx0 i, hxy i]
      have hz1 : ∀ i, z i ≤ 1 := fun i => by
        simp only [hz]; split_ifs <;> linarith [hy1 i, hxy i]
      have e1 : (fun w => if w ∈ insert v s then y w else x w) = Function.update z v (y v) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp
        · simp [hz, hw]
      have e2 : z = Function.update z v (x v) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp [hz, hv]
        · simp [Function.update_of_ne hw]
      rw [e1]
      calc F h (Function.update z v (y v)) ≤ F h (Function.update z v (x v)) :=
            dg_anti_step h hh z hz0 hz1 v _ _ (hxy v)
        _ = F h z := by rw [← e2]
        _ ≤ F h x := ih
  have := key Finset.univ
  simpa using this

theorem dgD_anti (f : Finset X → ℝ) (hf : Submodular f) (u : X) :
    ∀ S T, S ⊆ T → dgD f u T ≤ dgD f u S := by
  intro S T hST
  unfold dgD
  have h := hf (insert u S) (T.erase u)
  have e1 : insert u S ∪ T.erase u = insert u T := by
    ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (h | h)
      · rcases h with h | h
        · left; exact h
        · right; exact hST h
      · right; exact h.2
    · rintro (h | h)
      · left; left; exact h
      · by_cases hy : y = u
        · left; left; exact hy
        · right; exact ⟨hy, h⟩
  have e2 : insert u S ∩ T.erase u = S.erase u := by
    ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hh
      obtain ⟨h1, h2, h3⟩ := hh
      rcases h1 with h1 | h1
      · exact absurd h1 h2
      · exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨Or.inr h2, h1, hST h2⟩
  rw [e1, e2] at h
  linarith


noncomputable def dgT (a b : ℝ) : ℝ :=
  if max a 0 + max b 0 = 0 then 1 else max a 0 / (max a 0 + max b 0)

theorem dgT_bounds (a b : ℝ) : 0 ≤ dgT a b ∧ dgT a b ≤ 1 := by
  unfold dgT
  have ha := le_max_right a 0
  have hb := le_max_right b 0
  split_ifs with h
  · norm_num
  · have hp : 0 < max a 0 + max b 0 := lt_of_le_of_ne (by linarith) (Ne.symm h)
    constructor
    · positivity
    · rw [div_le_one hp]; linarith

theorem dgT_pos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : dgT a b = a / (a + b) := by
  unfold dgT
  rw [max_eq_left ha, max_eq_left hb.le, if_neg (by linarith)]

theorem dg_step_eq (f : Finset X → ℝ) (s : (X → ℝ) × (X → ℝ)) (u : X)
    (h1 : s.1 u = 0) (h2 : s.2 u = 1) :
    step f s u = (Function.update s.1 u (dgT (aGain f s.1 u) (bGain f s.2 u)),
      Function.update s.2 u (dgT (aGain f s.1 u) (bGain f s.2 u))) := by
  unfold step dgT
  simp only
  generalize aGain f s.1 u = a
  generalize bGain f s.2 u = b
  have key : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' →
      (1 - (if a' + b' = 0 then (0:ℝ) else b' / (a' + b'))) =
        (if a' + b' = 0 then 1 else a' / (a' + b')) := by
    intro a' b' ha hb
    split_ifs with h
    · ring
    · field_simp; ring
  have k2 := key (max a 0) (max b 0) (le_max_right _ _) (le_max_right _ _)
  generalize (if max a 0 + max b 0 = 0 then (1:ℝ) else max a 0 / (max a 0 + max b 0)) = T at k2 ⊢
  generalize (if max a 0 + max b 0 = 0 then (0:ℝ) else max b 0 / (max a 0 + max b 0)) = R at k2 ⊢
  ext v
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, indicator, Finset.mem_singleton]
    by_cases hv : v = u
    · subst hv; simp [h1]
    · simp [hv, Function.update_of_ne hv]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, indicator, Finset.mem_singleton]
    by_cases hv : v = u
    · subst hv; simp [h2, k2]
    · simp [hv, Function.update_of_ne hv]

theorem dg_aGain (f : Finset X → ℝ) (x : X → ℝ) (u : X) (h : x u = 0) :
    aGain f x u = F (dgD f u) x := by
  unfold aGain
  have e : x + indicator {u} = Function.update x u 1 := by
    funext v
    by_cases hv : v = u
    · subst hv; simp [indicator, h]
    · simp [indicator, hv, Function.update_of_ne hv]
  rw [e, dg_lin f x u 1, dg_lin' f x u, h]
  ring

theorem dg_bGain (f : Finset X → ℝ) (y : X → ℝ) (u : X) (h : y u = 1) :
    bGain f y u = - F (dgD f u) y := by
  unfold bGain
  have e : y - indicator {u} = Function.update y u 0 := by
    funext v
    by_cases hv : v = u
    · subst hv; simp [indicator, h]
    · simp [indicator, hv, Function.update_of_ne hv]
  rw [e, dg_lin' f y u, h]
  ring

theorem dg_state_succ (f : Finset X → ℝ) (l : List X) (k : ℕ) (hk : k < l.length) :
    state f l (k + 1) = step f (state f l k) (l[k]) := by
  unfold state
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

/-- the invariant -/
def dgInv (l : List X) (k : ℕ) (s : (X → ℝ) × (X → ℝ)) : Prop :=
  (∀ v, v ∈ l.take k → s.1 v = s.2 v ∧ 0 ≤ s.1 v ∧ s.1 v ≤ 1) ∧
  (∀ v, v ∉ l.take k → s.1 v = 0 ∧ s.2 v = 1)

theorem dg_notMem_take (l : List X) (hl : l.Nodup) (k : ℕ) (hk : k < l.length) :
    l[k] ∉ l.take k := by
  intro hm
  rw [List.mem_take_iff_getElem] at hm
  obtain ⟨j, hj, hjk⟩ := hm
  have := (hl.getElem_inj_iff (i := j) (j := k) (hi := by omega) (hj := hk)).mp hjk
  omega

theorem dg_inv (f : Finset X → ℝ) (l : List X) (hl : l.Nodup) :
    ∀ k, k ≤ l.length → dgInv l k (state f l k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun v hv => by simp at hv, fun v _ => ?_⟩
    simp [state]
  | succ k ih =>
    intro hk
    have hk' : k < l.length := by omega
    obtain ⟨I1, I2⟩ := ih (by omega)
    have hu := dg_notMem_take l hl k hk'
    obtain ⟨hx, hy⟩ := I2 _ hu
    rw [dg_state_succ f l k hk', dg_step_eq f _ _ hx hy]
    have hT := dgT_bounds (aGain f (state f l k).1 l[k]) (bGain f (state f l k).2 l[k])
    have htake : ∀ v, v ∈ l.take (k + 1) ↔ v ∈ l.take k ∨ v = l[k] := by
      intro v
      rw [List.take_succ_eq_append_getElem hk', List.mem_append, List.mem_singleton]
    constructor
    · intro v hv
      rcases (htake v).mp hv with h | h
      · have hne : v ≠ l[k] := fun e => hu (e ▸ h)
        simp only [Function.update_of_ne hne]
        exact I1 v h
      · subst h
        refine ⟨?_, ?_, ?_⟩ <;> simp [hT.1, hT.2]
    · intro v hv
      have h1 : v ∉ l.take k := fun h => hv ((htake v).mpr (Or.inl h))
      have hne : v ≠ l[k] := fun e => hv ((htake v).mpr (Or.inr e))
      simp only [Function.update_of_ne hne]
      exact I2 v h1

theorem dg_inv_bounds (l : List X) (k : ℕ) (s : (X → ℝ) × (X → ℝ)) (h : dgInv l k s) :
    (∀ v, 0 ≤ s.1 v) ∧ (∀ v, s.1 v ≤ s.2 v) ∧ (∀ v, s.2 v ≤ 1) := by
  have H : ∀ v, 0 ≤ s.1 v ∧ s.1 v ≤ s.2 v ∧ s.2 v ≤ 1 := by
    intro v
    by_cases hv : v ∈ l.take k
    · obtain ⟨e, h0, h1⟩ := h.1 v hv
      refine ⟨h0, le_of_eq e, ?_⟩; linarith
    · obtain ⟨e1, e2⟩ := h.2 v hv
      refine ⟨by linarith, by linarith, by linarith⟩
  exact ⟨fun v => (H v).1, fun v => (H v).2.1, fun v => (H v).2.2⟩

/-! generic one-step facts -/

theorem dg_ab_gen (f : Finset X → ℝ) (hf : Submodular f) (s : (X → ℝ) × (X → ℝ)) (u : X)
    (h0 : ∀ v, 0 ≤ s.1 v) (hxy : ∀ v, s.1 v ≤ s.2 v) (h1 : ∀ v, s.2 v ≤ 1)
    (hx : s.1 u = 0) (hy : s.2 u = 1) :
    0 ≤ aGain f s.1 u + bGain f s.2 u := by
  rw [dg_aGain f _ u hx, dg_bGain f _ u hy]
  have := dg_anti (dgD f u) (dgD_anti f hf u) s.1 s.2 h0 hxy h1
  linarith

theorem dg_real_A2 (a b D pu t : ℝ) (hab : 0 ≤ a + b) (hD1 : -b ≤ D) (hD2 : D ≤ a)
    (hpu : pu = 0 ∨ pu = 1) (ht : t = dgT a b) :
    (pu - t) * D ≤ 1 / 2 * (t * a + (1 - t) * b) := by
  have hT := dgT_bounds a b
  rw [← ht] at hT
  have h1 : (pu - t) * D ≤ max (t * b) ((1 - t) * a) := by
    rcases hpu with h | h <;> subst h
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_right (by nlinarith)
  refine le_trans h1 (max_le ?_ ?_)
  all_goals
    unfold dgT at ht
    rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
    · have : a = 0 := by linarith
      have : b = 0 := by linarith
      subst a; subst b; simp at ht; subst ht; norm_num
    · rw [max_eq_right ha, max_eq_left hb.le, if_neg (by linarith), zero_div] at ht
      subst ht; nlinarith
    · rw [max_eq_left ha.le, max_eq_right hb, if_neg (by linarith), add_zero, div_self ha.ne'] at ht
      subst ht; nlinarith
    · rw [max_eq_left ha.le, max_eq_left hb.le, if_neg (by linarith)] at ht
      have hp : 0 < a + b := by linarith
      have hta : t * (a + b) = a := by rw [ht]; field_simp
      have k1 : (a+b) * (t*a + b - 3*t*b) = (a-b)^2 := by linear_combination (a - 3*b) * hta
      have k2 : (a+b) * (3*t*a + b - 2*a - t*b) = (a-b)^2 := by linear_combination (3*a - b) * hta
      have q1 : 0 ≤ t*a + b - 3*t*b := by
        by_contra hc; push_neg at hc; nlinarith [sq_nonneg (a-b)]
      have q2 : 0 ≤ 3*t*a + b - 2*a - t*b := by
        by_contra hc; push_neg at hc; nlinarith [sq_nonneg (a-b)]
      nlinarith

theorem dg_real_6 (a b D pu t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hD1 : -b ≤ D) (hD2 : D ≤ a)
    (hpu : pu = 0 ∨ pu = 1) (ht : t = dgT a b) :
    (pu - t) * D ≤ a * b / (a + b) := by
  rw [dgT_pos a b ha hb] at ht
  have hp : 0 < a + b := by linarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : 1 - t = b / (a + b) := by rw [ht]; field_simp; ring
  rcases hpu with h | h <;> subst h
  · have : t * b = a * b / (a + b) := by rw [ht]; ring
    nlinarith
  · have h0 : 0 ≤ 1 - t := by rw [ht1]; positivity
    have : (1 - t) * a = a * b / (a + b) := by rw [ht1]; ring
    nlinarith


theorem dg_ind01 (O : Finset X) (v : X) : indicator O v = 0 ∨ indicator O v = 1 := by
  unfold indicator; split_ifs <;> simp

theorem dg_optI_step (f : Finset X → ℝ) (O : Finset X) (s : (X → ℝ) × (X → ℝ)) (u : X)
    (hx : s.1 u = 0) (hy : s.2 u = 1) :
    optI O (step f s u) = Function.update (optI O s) u
      (dgT (aGain f s.1 u) (bGain f s.2 u)) := by
  rw [dg_step_eq f s u hx hy]
  funext v
  by_cases hv : v = u
  · subst hv
    simp only [optI, Function.update_self]
    exact min_eq_right (le_max_right _ _)
  · simp [optI, Function.update_of_ne hv]

theorem dg_optI_bounds (O : Finset X) (s : (X → ℝ) × (X → ℝ))
    (hxy : ∀ v, s.1 v ≤ s.2 v) (v : X) :
    s.1 v ≤ optI O s v ∧ optI O s v ≤ s.2 v := by
  unfold optI
  exact ⟨le_min (le_max_right _ _) (hxy v), min_le_right _ _⟩

theorem dg_optI_u (O : Finset X) (s : (X → ℝ) × (X → ℝ)) (u : X)
    (hx : s.1 u = 0) (hy : s.2 u = 1) : optI O s u = indicator O u := by
  unfold optI
  rw [hx, hy]
  rcases dg_ind01 O u with h | h <;> rw [h] <;> norm_num

theorem dg_gen (f : Finset X → ℝ) (hf : Submodular f) (O : Finset X)
    (s : (X → ℝ) × (X → ℝ)) (u : X)
    (h0 : ∀ v, 0 ≤ s.1 v) (hxy : ∀ v, s.1 v ≤ s.2 v) (h1 : ∀ v, s.2 v ≤ 1)
    (hx : s.1 u = 0) (hy : s.2 u = 1) :
    ∃ D : ℝ, -bGain f s.2 u ≤ D ∧ D ≤ aGain f s.1 u ∧
      F f (optI O s) - F f (optI O (step f s u)) =
        (indicator O u - dgT (aGain f s.1 u) (bGain f s.2 u)) * D ∧
      F f (step f s u).1 - F f s.1 = dgT (aGain f s.1 u) (bGain f s.2 u) * aGain f s.1 u ∧
      F f (step f s u).2 - F f s.2 =
        (1 - dgT (aGain f s.1 u) (bGain f s.2 u)) * bGain f s.2 u := by
  have hopt := dg_optI_step f O s u hx hy
  have hPu := dg_optI_u O s u hx hy
  have hstep := dg_step_eq f s u hx hy
  rw [hopt, hstep]
  simp only
  rw [dg_aGain f _ u hx, dg_bGain f _ u hy]
  generalize dgT (F (dgD f u) s.1) (-F (dgD f u) s.2) = t
  set P := optI O s with hP
  have hPb := dg_optI_bounds O s hxy
  refine ⟨F (dgD f u) P, ?_, ?_, ?_, ?_, ?_⟩
  · have := dg_anti (dgD f u) (dgD_anti f hf u) P s.2 (fun v => le_trans (h0 v) (hPb v).1)
      (fun v => (hPb v).2) h1
    linarith
  · exact dg_anti (dgD f u) (dgD_anti f hf u) s.1 P h0 (fun v => (hPb v).1)
      (fun v => le_trans (hPb v).2 (h1 v))
  · have e1 := dg_lin' f P u
    have e2 := dg_lin f P u t
    rw [hPu] at e1
    rw [e1, e2]; ring
  · have e1 := dg_lin' f s.1 u
    have e2 := dg_lin f s.1 u t
    rw [hx] at e1
    rw [e1, e2]; ring
  · have e1 := dg_lin' f s.2 u
    have e2 := dg_lin f s.2 u t
    rw [hy] at e1
    rw [e1, e2]; ring

theorem dg_ctx (f : Finset X → ℝ) (l : List X) (hl : l.Nodup) (k : ℕ) (hk : k < l.length) :
    (∀ v, 0 ≤ (state f l k).1 v) ∧ (∀ v, (state f l k).1 v ≤ (state f l k).2 v) ∧
      (∀ v, (state f l k).2 v ≤ 1) ∧ (state f l k).1 l[k] = 0 ∧ (state f l k).2 l[k] = 1 := by
  have hI := dg_inv f l hl k hk.le
  obtain ⟨a1, a2, a3⟩ := dg_inv_bounds l k _ hI
  obtain ⟨b1, b2⟩ := hI.2 _ (dg_notMem_take l hl k hk)
  exact ⟨a1, a2, a3, b1, b2⟩

theorem dg_A2_k (f : Finset X → ℝ) (hf : Submodular f) (l : List X) (hl : l.Nodup)
    (O : Finset X) (k : ℕ) (hk : k < l.length) :
    F f (optI O (state f l k)) - F f (optI O (state f l (k + 1)))
      ≤ 1 / 2 * (F f (state f l (k + 1)).1 - F f (state f l k).1
          + F f (state f l (k + 1)).2 - F f (state f l k).2) := by
  obtain ⟨h0, hxy, h1, hx, hy⟩ := dg_ctx f l hl k hk
  rw [dg_state_succ f l k hk]
  obtain ⟨D, hD1, hD2, e1, e2, e3⟩ := dg_gen f hf O _ _ h0 hxy h1 hx hy
  have hab := dg_ab_gen f hf _ _ h0 hxy h1 hx hy
  have := dg_real_A2 _ _ D _ _ hab hD1 hD2 (dg_ind01 O l[k]) rfl
  linarith

theorem dg_ab_core (f : Finset X → ℝ) (hf : Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
      + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨h0, hxy, h1, hx, hy⟩ := dg_ctx f l hl k (by omega)
  exact dg_ab_gen f hf _ _ h0 hxy h1 hx hy

theorem dg_ineq6_core (f : Finset X → ℝ) (hf : Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length)
    (ha : 0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)))
    (hb : 0 < bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) :
    F f (optI O (state f l (i - 1)))
        - F f (optI O (state f l i))
      ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
          * bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))
        / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
            + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ha hb ⊢
  have hk : k < l.length := by omega
  obtain ⟨h0, hxy, h1, hx, hy⟩ := dg_ctx f l hl k hk
  rw [dg_state_succ f l k hk]
  obtain ⟨D, hD1, hD2, e1, e2, e3⟩ := dg_gen f hf O _ _ h0 hxy h1 hx hy
  have := dg_real_6 _ _ D _ _ ha hb hD1 hD2 (dg_ind01 O l[k]) rfl
  linarith

theorem dg_A2_core (f : Finset X → ℝ) (hf : Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    F f (optI O (state f l (i - 1)))
        - F f (optI O (state f l i))
      ≤ 1 / 2 * (F f (state f l i).1
          - F f (state f l (i - 1)).1
          + F f (state f l i).2
          - F f (state f l (i - 1)).2) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact dg_A2_k f hf l hl O k (by omega)

theorem dg_F_ind (f : Finset X → ℝ) (O : Finset X) : F f (indicator O) = f O := by
  unfold F
  rw [Finset.sum_eq_single O]
  · have : ∀ i, (if i ∈ O then indicator O i else 1 - indicator O i) = 1 := by
      intro i; unfold indicator; split_ifs <;> norm_num
    simp [this]
  · intro S _ hSO
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero_iff.mpr
    have : ∃ i, ¬ (i ∈ S ↔ i ∈ O) := by
      by_contra hc
      push_neg at hc
      exact hSO (Finset.ext hc)
    obtain ⟨i, hi⟩ := this
    refine ⟨i, Finset.mem_univ _, ?_⟩
    unfold indicator
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ O <;> simp_all
  · intro h; exact absurd (Finset.mem_univ O) h

theorem dg_state0 (f : Finset X → ℝ) (l : List X) : state f l 0 = (0, 1) := by
  simp [state]

theorem dg_tele_core (f : Finset X → ℝ) (hf : Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    F f (optI O (state f l 0))
        - F f (optI O (state f l l.length))
      ≤ 1 / 2 * (F f (state f l l.length).1
            - F f (state f l 0).1)
        + 1 / 2 * (F f (state f l l.length).2
            - F f (state f l 0).2) ∧
    1 / 2 * (F f (state f l l.length).1
            - F f (state f l 0).1)
        + 1 / 2 * (F f (state f l l.length).2
            - F f (state f l 0).2)
      ≤ (F f (state f l l.length).1
          + F f (state f l l.length).2) / 2 := by
  have key : ∀ k, k ≤ l.length →
      F f (optI O (state f l 0)) - F f (optI O (state f l k))
        ≤ 1 / 2 * (F f (state f l k).1 - F f (state f l 0).1)
          + 1 / 2 * (F f (state f l k).2 - F f (state f l 0).2) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := dg_A2_k f hf l hl O k (by omega)
      have := ih (by omega)
      linarith
  refine ⟨key _ le_rfl, ?_⟩
  have e0 : (0 : X → ℝ) = indicator ∅ := by funext v; simp [indicator]
  have e1 : (1 : X → ℝ) = indicator Finset.univ := by funext v; simp [indicator]
  rw [dg_state0]
  simp only
  rw [e0, e1, dg_F_ind, dg_F_ind]
  linarith [hf0 ∅, hf0 Finset.univ]

theorem dg_goal_core (f : Finset X → ℝ) (hf : Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (state f l l.length).1 = (state f l l.length).2 ∧
    OPT f ≤ 2 * F f (state f l l.length).1 := by
  have hI := dg_inv f l hl l.length le_rfl
  have heq : (state f l l.length).1 = (state f l l.length).2 := by
    funext v
    exact (hI.1 v (by rw [List.take_length]; exact hcov v)).1
  refine ⟨heq, ?_⟩
  obtain ⟨O, -, hOeq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Finset X)) f
  have hO : ∀ S, f S ≤ f O := fun S => by
    rw [← hOeq]; exact Finset.le_sup' f (Finset.mem_univ S)
  have ht := (dg_tele_core f hf hf0 l hl hcov O hO)
  have h0 : optI O (state f l 0) = indicator O := by
    rw [dg_state0]; funext v; unfold optI
    rcases dg_ind01 O v with h | h <;> simp [h]
  have hn : optI O (state f l l.length) = (state f l l.length).1 := by
    funext v; unfold optI; rw [← heq]
    exact min_eq_right (le_max_right _ _)
  rw [h0, hn, dg_F_ind, ← heq] at ht
  unfold OPT
  rw [hOeq]
  linarith [ht.1, ht.2]

end dgsec

end DoubleGreedyUSM.Fractional

open DoubleGreedyUSM.Fractional


theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
      + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) := by
  exact dg_ab_core f hf l hl hcov i hi1 hin
