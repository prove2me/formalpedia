-- Prove2me | solution 1 for CycleCanceling.MinMean.minMean_run_length_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T20:26:01.655908+00:00
-- url     : https://prove2.me/submissions/56748fd9-6e1e-4678-8c53-3ceabc591e64

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_Algorithm
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CC579

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]


open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- consecutive pairs of a list -/
def pA : List V → List (V × V)
  | a :: b :: l => (a, b) :: pA (b :: l)
  | _ => []

theorem pA_split (l1 : List V) (x : V) (l2 : List V) :
    pA (l1 ++ x :: l2) = pA (l1 ++ [x]) ++ pA (x :: l2) := by
  induction l1 with
  | nil => simp [pA]
  | cons a l1 ih =>
    cases l1 with
    | nil => simp [pA]
    | cons b l1 =>
      simp only [List.cons_append, pA] at ih ⊢
      rw [ih]

theorem zip_pA (L : List V) (x y : V) :
    List.zip (x :: L) (L ++ [y]) = pA (x :: (L ++ [y])) := by
  induction L generalizing x with
  | nil => simp [pA]
  | cons b L ih =>
    simp only [List.cons_append, List.zip_cons_cons, pA]
    rw [← ih]

theorem cycleArcs_cons (x : V) (L : List V) :
    cycleArcs (x :: L) = pA (x :: (L ++ [x])) := by
  unfold cycleArcs
  rw [List.rotate_cons_succ, List.rotate_zero, zip_pA]

theorem exists_delta {α : Type*} (L : List α) (r : α → ℝ) (h : ∀ a ∈ L, 0 < r a) :
    ∃ δ > 0, ∀ a ∈ L, δ ≤ r a := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
    obtain ⟨δ, hδ, hδL⟩ := ih (fun b hb => h b (by simp [hb]))
    refine ⟨min δ (r a), lt_min hδ (h a (by simp)), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδL b hb)

/-- the unit flow along a list of arcs -/
def dL (L : List (V × V)) (v w : V) : ℝ :=
  (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))).sum

theorem dL_antisymm (L : List (V × V)) (v w : V) : dL L v w = - dL L w v := by
  unfold dL
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

theorem dL_le_length (L : List (V × V)) (v w : V) : dL L v w ≤ L.length := by
  unfold dL
  have := List.sum_le_card_nsmul
    (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))) 1
    (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      split_ifs <;> norm_num)
  simpa using this

theorem dL_nonpos (L : List (V × V)) (v w : V) (h : (v, w) ∉ L) : dL L v w ≤ 0 := by
  unfold dL
  have := List.sum_le_card_nsmul
    (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))) 0
    (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have : a ≠ (v, w) := fun e => h (e ▸ ha)
      split_ifs <;> simp_all)
  simpa using this

theorem dL_cost (N : CircNetwork V) (L : List (V × V)) (hL : ∀ a ∈ L, a ∈ N.E) :
    ∑ a ∈ N.E, N.c a.1 a.2 * dL L a.1 a.2 = 2 * (L.map (fun a => N.c a.1 a.2)).sum := by
  induction L with
  | nil => simp [dL]
  | cons b L ih =>
    have hb : b ∈ N.E := hL b (by simp)
    have ih' := ih (fun a ha => hL a (by simp [ha]))
    have hsplit : ∀ a : V × V, dL (b :: L) a.1 a.2 =
        ((if b = (a.1, a.2) then (1:ℝ) else 0) - (if b = (a.2, a.1) then 1 else 0)) +
          dL L a.1 a.2 := by
      intro a; simp [dL]
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib, ih', mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ a ∈ N.E, N.c a.1 a.2 * (if b = (a.1, a.2) then (1:ℝ) else 0) = N.c b.1 b.2 := by
      simp only [Prod.mk.eta, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq N.E b]; simp [hb]
    have e2 : ∑ a ∈ N.E, N.c a.1 a.2 * (if b = (a.2, a.1) then (1:ℝ) else 0) = - N.c b.1 b.2 := by
      have : ∀ a : V × V, (b = (a.2, a.1)) ↔ (a = b.swap) := by
        intro a; constructor
        · rintro rfl; simp
        · rintro rfl; simp
      simp only [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' N.E b.swap]
      have hs : b.swap ∈ N.E := by
        have := (N.symm b.1 b.2).mp (by simpa using hb); simpa [Prod.swap] using this
      simp only [hs, if_true, Prod.fst_swap, Prod.snd_swap]
      rw [N.cost_antisymm b.2 b.1 (by simpa [Prod.swap] using hs)]
    rw [e1, e2]; simp; ring

theorem dL_div (N : CircNetwork V) (L : List (V × V)) (hL : ∀ a ∈ L, a ∈ N.E) (w : V) :
    ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), dL L v w =
      (L.map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum := by
  induction L with
  | nil => simp [dL]
  | cons b L ih =>
    have hb : b ∈ N.E := hL b (by simp)
    have ih' := ih (fun a ha => hL a (by simp [ha]))
    have hsplit : ∀ v, dL (b :: L) v w =
        ((if b = (v, w) then (1:ℝ) else 0) - (if b = (w, v) then 1 else 0)) + dL L v w := by
      intro v; simp [dL]
    simp_rw [hsplit, Finset.sum_add_distrib, ih', Finset.sum_sub_distrib]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    obtain ⟨x, y⟩ := b
    simp only [Prod.mk.injEq]
    congr 1
    · by_cases hy : y = w
      · subst hy
        have hx : (y, x) ∈ N.E := (N.symm x y).mp hb
        rw [Finset.sum_eq_single x]
        · simp [hx]
        · intro v _ hv; simp [Ne.symm hv]
        · intro hx'; simp [hx] at hx'
      · simp [hy]
    · by_cases hx : x = w
      · subst hx
        rw [Finset.sum_eq_single y]
        · simp [hb]
        · intro v _ hv; simp [Ne.symm hv]
        · intro hy'; simp [hb] at hy'
      · simp [hx]

theorem cycle_div (Γ : List V) (w : V) :
    ((cycleArcs Γ).map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum
      = 0 := by
  have hlen : Γ.length = (Γ.rotate 1).length := by simp
  have h1 : (cycleArcs Γ).map Prod.fst = Γ := by
    unfold cycleArcs; exact List.map_fst_zip (le_of_eq hlen)
  have h2 : (cycleArcs Γ).map Prod.snd = Γ.rotate 1 := by
    unfold cycleArcs; exact List.map_snd_zip (le_of_eq hlen.symm)
  have hs : ∀ (L : List (V × V)),
      (L.map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum =
      ((L.map Prod.snd).map (fun x => if x = w then (1:ℝ) else 0)).sum -
      ((L.map Prod.fst).map (fun x => if x = w then (1:ℝ) else 0)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  rw [hs, h1, h2]
  have := ((List.rotate_perm Γ 1).map (fun x => if x = w then (1:ℝ) else 0)).sum_eq
  rw [this]; ring

/-- the potential argument: sum of potential differences against a circulation difference -/
theorem pot_zero (N : CircNetwork V) (h : V → V → ℝ) (p : V → ℝ)
    (hanti : ∀ v w, (v, w) ∈ N.E → h v w = -h w v)
    (hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), h v w = 0) :
    ∑ a ∈ N.E, (p a.1 - p a.2) * h a.1 a.2 = 0 := by
  have hE : ∀ F : V × V → ℝ, ∑ a ∈ N.E, F a =
      ∑ x, ∑ y, if (x, y) ∈ N.E then F (x, y) else 0 := by
    intro F
    rw [← Fintype.sum_prod_type (fun a => if a ∈ N.E then F a else 0)]
    rw [Finset.sum_ite_mem]; simp
  have A : ∀ x, ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) = 0 := by
    intro x
    have : ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) =
        - p x * ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs with hy
      · rw [hanti x y hy]; ring
      · rfl
    rw [this, hcons x, mul_zero]
  have B : ∀ y, ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) = 0 := by
    intro y
    have : ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) =
        p y * ∑ x ∈ Finset.univ.filter (fun x => (y, x) ∈ N.E), h x y := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hxy : (x, y) ∈ N.E
      · simp [hxy, (N.symm x y).mp hxy]
      · have : (y, x) ∉ N.E := fun h' => hxy ((N.symm y x).mp h')
        simp [hxy, this]
    rw [this, hcons y, mul_zero]
  rw [hE]
  dsimp only
  calc ∑ x, ∑ y, (if (x, y) ∈ N.E then (p x - p y) * h x y else 0)
      = ∑ x, ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) -
          ∑ y, ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) := by
        rw [Finset.sum_comm (f := fun y x => if (x, y) ∈ N.E then p y * h x y else 0)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> ring
    _ = 0 := by simp [A, B]

/-- weighted path / cycle sums -/
noncomputable def pathW (wt : V → V → ℝ) (P : List V) : ℝ :=
  ((pA P).map (fun a => wt a.1 a.2)).sum

noncomputable def cycW (wt : V → V → ℝ) (Γ : List V) : ℝ :=
  ((cycleArcs Γ).map (fun a => wt a.1 a.2)).sum

def Res (N : CircNetwork V) (f : V → V → ℝ) (P : List V) : Prop :=
  ∀ a ∈ pA P, a ∈ N.E ∧ 0 < resCap N f a.1 a.2

def S (N : CircNetwork V) (f : V → V → ℝ) (v : V) : Set (List V) :=
  {Q | (Q ++ [v]).Nodup ∧ Res N f (Q ++ [v])}

theorem S_finite (N : CircNetwork V) (f : V → V → ℝ) (v : V) : (S N f v).Finite := by
  refine (List.finite_length_le V (Fintype.card V)).subset (fun Q hQ => ?_)
  have := hQ.1.length_le_card
  simp only [List.length_append, List.length_singleton] at this
  show Q.length ≤ Fintype.card V
  omega

theorem pA_snoc2 (Q : List V) (v w : V) : pA ((Q ++ [v]) ++ [w]) = pA (Q ++ [v]) ++ [(v, w)] := by
  have : (Q ++ [v]) ++ [w] = Q ++ v :: [w] := by simp
  rw [this, pA_split]; simp [pA]

theorem exists_pot_w (N : CircNetwork V) (f : V → V → ℝ) (wt : V → V → ℝ)
    (hneg : ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycW wt Γ < 0) :
    ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → p w ≤ p v + wt v w := by
  have hex : ∀ v, ∃ Q ∈ S N f v, ∀ Q' ∈ S N f v,
      pathW wt (Q ++ [v]) ≤ pathW wt (Q' ++ [v]) := by
    intro v
    refine Set.exists_min_image (S N f v) (fun Q => pathW wt (Q ++ [v])) (S_finite N f v)
      ⟨[], ?_, ?_⟩
    · simp
    · intro a ha; simp [pA] at ha
  choose Q hQ hmin using hex
  refine ⟨fun v => pathW wt (Q v ++ [v]), ?_⟩
  intro v w hvw hres
  dsimp only
  by_cases hw : w ∈ Q v ++ [v]
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hw
    have hsplit := pA_split A w B
    have hext : pA ((A ++ w :: B) ++ [w]) = pA (A ++ w :: B) ++ [(v, w)] := by
      rw [← hAB]; exact pA_snoc2 _ _ _
    have hext2 : pA ((A ++ w :: B) ++ [w]) = pA (A ++ [w]) ++ pA (w :: (B ++ [w])) := by
      have : (A ++ w :: B) ++ [w] = A ++ w :: (B ++ [w]) := by simp
      rw [this, pA_split]
    have hcyc : pA (w :: (B ++ [w])) = pA (w :: B) ++ [(v, w)] := by
      rw [hext, hsplit, List.append_assoc] at hext2
      exact (List.append_cancel_left hext2).symm
    have hnd : (A ++ w :: B).Nodup := hAB ▸ (hQ v).1
    have hR : Res N f (A ++ w :: B) := hAB ▸ (hQ v).2
    have hA : A ∈ S N f w := by
      refine ⟨?_, ?_⟩
      · have : A ++ w :: B = (A ++ [w]) ++ B := by simp
        rw [this] at hnd
        exact hnd.sublist (List.sublist_append_left _ _)
      · intro a ha; exact hR a (by rw [hsplit]; exact List.mem_append_left _ ha)
    have hcycle : IsResidualCycle N f (w :: B) := by
      refine ⟨List.cons_ne_nil _ _, hnd.sublist (List.sublist_append_right _ _), ?_⟩
      intro a ha
      rw [cycleArcs_cons, hcyc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hR a (by rw [hsplit]; exact List.mem_append_right _ ha)
      · simp at ha; subst ha; exact ⟨hvw, hres⟩
    have hcost : 0 ≤ cycW wt (w :: B) := by
      by_contra hc; exact hneg ⟨w :: B, hcycle, lt_of_not_ge hc⟩
    have hcc : cycW wt (w :: B) = pathW wt (w :: B) + wt v w := by
      unfold cycW pathW; rw [cycleArcs_cons, hcyc]; simp
    have hpv : pathW wt (Q v ++ [v]) = pathW wt (A ++ [w]) + pathW wt (w :: B) := by
      unfold pathW; rw [hAB, hsplit]; simp
    have := hmin w A hA
    linarith
  · have hS : Q v ++ [v] ∈ S N f w := by
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨(hQ v).1, List.nodup_singleton w, ?_⟩
        simp only [List.mem_singleton]
        rintro a ha b rfl rfl; exact hw ha
      · intro a ha
        rw [pA_snoc2] at ha
        rcases List.mem_append.mp ha with ha | ha
        · exact (hQ v).2 a ha
        · simp at ha; subst ha; exact ⟨hvw, hres⟩
    have := hmin w _ hS
    have e : pathW wt ((Q v ++ [v]) ++ [w]) = pathW wt (Q v ++ [v]) + wt v w := by
      unfold pathW; rw [pA_snoc2]; simp
    linarith


theorem exists_pot (N : CircNetwork V) (f : V → V → ℝ)
    (hneg : ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycleCost N Γ < 0) :
    ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → p w ≤ p v + N.c v w :=
  exists_pot_w N f N.c hneg


theorem thm21 {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsMinCost N f ↔ ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycleCost N Γ < 0 := by
  constructor
  · rintro ⟨-, hmin⟩ ⟨Γ, hΓ, hneg⟩
    set L := cycleArcs Γ with hLdef
    have hLE : ∀ a ∈ L, a ∈ N.E := fun a ha => (hΓ.2.2 a ha).1
    obtain ⟨δ, hδ, hδL⟩ := exists_delta L (fun a => resCap N f a.1 a.2)
      (fun a ha => (hΓ.2.2 a ha).2)
    have hlen : L.length = Γ.length := by
      rw [hLdef]; unfold cycleArcs; simp
    have hlpos : (0 : ℝ) < L.length := by
      rw [hlen]; exact_mod_cast List.length_pos_of_ne_nil hΓ.1
    set ε := δ / L.length with hε
    have hεpos : 0 < ε := div_pos hδ hlpos
    let g : V → V → ℝ := fun v w => f v w + ε * dL L v w
    have hg : IsCirculation N g := by
      refine ⟨?_, ?_, ?_⟩
      · intro v w hvw
        show f v w + ε * dL L v w ≤ N.u v w
        by_cases hm : (v, w) ∈ L
        · have h1 := hδL _ hm
          have h2 : ε * dL L v w ≤ ε * L.length :=
            mul_le_mul_of_nonneg_left (dL_le_length L v w) hεpos.le
          have h3 : ε * L.length = δ := by rw [hε]; field_simp
          simp only [resCap] at h1
          linarith
        · have := mul_nonpos_of_nonneg_of_nonpos hεpos.le (dL_nonpos L v w hm)
          linarith [hf.1 v w hvw]
      · intro v w hvw
        show f v w + ε * dL L v w = -(f w v + ε * dL L w v)
        rw [hf.2.1 v w hvw, dL_antisymm L v w]; ring
      · intro w
        show ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), (f v w + ε * dL L v w) = 0
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, dL_div N L hLE w, hf.2.2 w]
        rw [hLdef, cycle_div]; ring
    have hc := hmin g hg
    have hcg : cost N g = cost N f + ε * cycleCost N Γ := by
      unfold cost
      show (1 / 2 : ℝ) * ∑ a ∈ N.E, N.c a.1 a.2 * (f a.1 a.2 + ε * dL L a.1 a.2) = _
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have : ∑ a ∈ N.E, N.c a.1 a.2 * (ε * dL L a.1 a.2) =
          ε * ∑ a ∈ N.E, N.c a.1 a.2 * dL L a.1 a.2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_); ring
      rw [this, dL_cost N L hLE]
      unfold cycleCost; rw [← hLdef]; ring
    have : ε * cycleCost N Γ < 0 := mul_neg_of_pos_of_neg hεpos hneg
    linarith
  · intro hneg
    refine ⟨hf, fun g hg => ?_⟩
    obtain ⟨p, hp⟩ := exists_pot N f hneg
    let h : V → V → ℝ := fun v w => g v w - f v w
    have hanti : ∀ v w, (v, w) ∈ N.E → h v w = -h w v := by
      intro v w hvw; show g v w - f v w = -(g w v - f w v)
      rw [hg.2.1 v w hvw, hf.2.1 v w hvw]; ring
    have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), h v w = 0 := by
      intro w; show ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), (g v w - f v w) = 0
      rw [Finset.sum_sub_distrib, hg.2.2 w, hf.2.2 w]; ring
    have hz := pot_zero N h p hanti hcons
    have hnn : 0 ≤ ∑ a ∈ N.E, (N.c a.1 a.2 + p a.1 - p a.2) * h a.1 a.2 := by
      refine Finset.sum_nonneg (fun a ha => ?_)
      obtain ⟨v, w⟩ := a
      show 0 ≤ (N.c v w + p v - p w) * (g v w - f v w)
      rcases lt_trichotomy (g v w) (f v w) with hlt | heq | hgt
      · have hwv : (w, v) ∈ N.E := (N.symm v w).mp ha
        have hres : 0 < resCap N f w v := by
          simp only [resCap]
          have := hg.1 w v hwv
          rw [hg.2.1 v w ha] at hlt; rw [hf.2.1 v w ha] at hlt
          linarith
        have := hp w v hwv hres
        rw [N.cost_antisymm w v hwv] at this
        nlinarith
      · rw [heq]; simp
      · have hres : 0 < resCap N f v w := by
          simp only [resCap]; linarith [hg.1 v w ha]
        have := hp v w ha hres
        nlinarith
    have hsplit : ∑ a ∈ N.E, (N.c a.1 a.2 + p a.1 - p a.2) * h a.1 a.2 =
        ∑ a ∈ N.E, N.c a.1 a.2 * h a.1 a.2 + ∑ a ∈ N.E, (p a.1 - p a.2) * h a.1 a.2 := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun a _ => ?_); ring
    have hdiff : ∑ a ∈ N.E, N.c a.1 a.2 * h a.1 a.2 =
        ∑ a ∈ N.E, N.c a.1 a.2 * g a.1 a.2 - ∑ a ∈ N.E, N.c a.1 a.2 * f a.1 a.2 := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun a _ => ?_)
      show N.c a.1 a.2 * (g a.1 a.2 - f a.1 a.2) = _; ring
    unfold cost
    linarith


/-! ## Part 2: cycle capacity, cancel formula, N1 -/

theorem foldr_min_spec {α : Type*} (r : α → ℝ) (l : List α) (x : ℝ) :
    l.foldr (fun b acc => min (r b) acc) x ≤ x ∧
    (∀ b ∈ l, l.foldr (fun b acc => min (r b) acc) x ≤ r b) ∧
    (l.foldr (fun b acc => min (r b) acc) x = x ∨
      ∃ b ∈ l, l.foldr (fun b acc => min (r b) acc) x = r b) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(min_le_right _ _).trans h1, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (h2 c hc)
    · rcases min_choice (r b) (l.foldr (fun b acc => min (r b) acc) x) with h | h
      · right; exact ⟨b, by simp, h⟩
      · rw [h]
        rcases h3 with h3 | ⟨c, hc, h3⟩
        · left; exact h3
        · right; exact ⟨c, List.mem_cons_of_mem _ hc, h3⟩

theorem cycleCap_spec (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V)
    (hne : cycleArcs Γ ≠ []) :
    (∀ a ∈ cycleArcs Γ, cycleCap N f Γ ≤ resCap N f a.1 a.2) ∧
    ∃ a ∈ cycleArcs Γ, cycleCap N f Γ = resCap N f a.1 a.2 := by
  unfold cycleCap
  cases hc : cycleArcs Γ with
  | nil => exact absurd hc hne
  | cons a l =>
    obtain ⟨h1, h2, h3⟩ := foldr_min_spec (fun b : V × V => resCap N f b.1 b.2) l
      (resCap N f a.1 a.2)
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · exact h2 b hb
    · rcases h3 with h3 | ⟨b, hb, h3⟩
      · exact ⟨a, by simp, h3⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb, h3⟩

theorem cycleArcs_ne_nil {Γ : List V} (h : Γ ≠ []) : cycleArcs Γ ≠ [] := by
  intro hc
  apply h
  have : (cycleArcs Γ).length = Γ.length := by unfold cycleArcs; simp
  rw [hc] at this
  exact List.length_eq_zero_iff.mp this.symm

theorem cycleCap_pos (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V)
    (hΓ : IsResidualCycle N f Γ) : 0 < cycleCap N f Γ := by
  obtain ⟨-, ⟨a, ha, h⟩⟩ := cycleCap_spec N f Γ (cycleArcs_ne_nil hΓ.1)
  rw [h]; exact (hΓ.2.2 a ha).2

theorem dL_eq_count (L : List (V × V)) (v w : V) :
    dL L v w = (L.count (v, w) : ℝ) - (L.count (w, v) : ℝ) := by
  induction L with
  | nil => simp [dL]
  | cons a L ih =>
    have : dL (a :: L) v w = ((if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))
        + dL L v w := by simp [dL]
    rw [this, ih]
    by_cases h1 : a = (v, w) <;> by_cases h2 : a = (w, v) <;> simp [List.count_cons, h1, h2] <;> ring

theorem cancel_eq (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) (v w : V) :
    cancel N f Γ v w = f v w + cycleCap N f Γ * dL (cycleArcs Γ) v w := by
  unfold cancel
  rw [dL_eq_count]; ring

theorem cycleArcs_nodup {Γ : List V} (h : Γ.Nodup) : (cycleArcs Γ).Nodup := by
  have hlen : Γ.length = (Γ.rotate 1).length := by simp
  have h1 : (cycleArcs Γ).map Prod.fst = Γ := by
    unfold cycleArcs; exact List.map_fst_zip (le_of_eq hlen)
  have h2 : ((cycleArcs Γ).map Prod.fst).Nodup := by rw [h1]; exact h
  exact List.Nodup.of_map Prod.fst h2

theorem cancel_isCirculation (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsResidualCycle N f Γ) : IsCirculation N (cancel N f Γ) := by
  set L := cycleArcs Γ with hLdef
  have hLE : ∀ a ∈ L, a ∈ N.E := fun a ha => (hΓ.2.2 a ha).1
  have hδ := cycleCap_pos N f Γ hΓ
  obtain ⟨hδL, -⟩ := cycleCap_spec N f Γ (cycleArcs_ne_nil hΓ.1)
  have hnd : L.Nodup := cycleArcs_nodup hΓ.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro v w hvw
    rw [cancel_eq]
    by_cases hm : (v, w) ∈ L
    · have h1 := hδL _ hm
      have h2 : dL L v w ≤ 1 := by
        rw [dL_eq_count]
        have := List.nodup_iff_count_le_one.mp hnd (v, w)
        have h3 : (L.count (v, w) : ℝ) ≤ 1 := by exact_mod_cast this
        have h4 : (0:ℝ) ≤ (L.count (w, v) : ℝ) := Nat.cast_nonneg _
        linarith
      have h5 : cycleCap N f Γ * dL L v w ≤ cycleCap N f Γ := by nlinarith
      simp only [resCap] at h1
      linarith
    · have := mul_nonpos_of_nonneg_of_nonpos hδ.le (dL_nonpos L v w hm)
      linarith [hf.1 v w hvw]
  · intro v w hvw
    rw [cancel_eq, cancel_eq, hf.2.1 v w hvw, dL_antisymm L v w]; ring
  · intro w
    have : ∀ v, cancel N f Γ v w = f v w + cycleCap N f Γ * dL L v w := fun v => cancel_eq _ _ _ _ _
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, dL_div N L hLE w, hf.2.2 w]
    rw [hLdef, cycle_div]; ring

theorem run_isCirculation (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ)
    (hrun : IsMinMeanRun N F K) (i : ℕ) (hi : i ≤ K) : IsCirculation N (F i) := by
  induction i with
  | zero => exact hrun.1
  | succ i ih =>
    have hi' : i < K := by omega
    obtain ⟨Γ, hΓ, -, hF⟩ := hrun.2 i hi'
    rw [hF]
    exact cancel_isCirculation N (F i) (ih (by omega)) Γ hΓ.1

/-! ## Part 3: epsilon-optimality, Theorem 3.3 core, Lemma 3.5 core -/

theorem cycleArcs_length (Γ : List V) : (cycleArcs Γ).length = Γ.length := by
  unfold cycleArcs; simp

theorem cycle_pot_sum (p : V → ℝ) (Γ : List V) :
    ((cycleArcs Γ).map (fun a => p a.1 - p a.2)).sum = 0 := by
  have hlen : Γ.length = (Γ.rotate 1).length := by simp
  have h1 : (cycleArcs Γ).map Prod.fst = Γ := by
    unfold cycleArcs; exact List.map_fst_zip (le_of_eq hlen)
  have h2 : (cycleArcs Γ).map Prod.snd = Γ.rotate 1 := by
    unfold cycleArcs; exact List.map_snd_zip (le_of_eq hlen.symm)
  have hs : ∀ (L : List (V × V)),
      (L.map (fun a => p a.1 - p a.2)).sum =
      ((L.map Prod.fst).map p).sum - ((L.map Prod.snd).map p).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  rw [hs, h1, h2]
  have := ((List.rotate_perm Γ 1).map p).sum_eq
  rw [this]; ring

theorem cycle_reduced_sum (N : CircNetwork V) (p : V → ℝ) (Γ : List V) :
    ((cycleArcs Γ).map (fun a => reducedCost N p a.1 a.2)).sum = cycleCost N Γ := by
  unfold cycleCost reducedCost
  have : ∀ a : V × V, N.c a.1 a.2 + p a.1 - p a.2 = N.c a.1 a.2 + (p a.1 - p a.2) := by
    intro a; ring
  simp_rw [this]
  rw [List.sum_map_add, cycle_pot_sum]; ring

theorem reducedCost_antisymm (N : CircNetwork V) (p : V → ℝ) (v w : V) (h : (v, w) ∈ N.E) :
    reducedCost N p v w = - reducedCost N p w v := by
  unfold reducedCost
  rw [N.cost_antisymm v w h]; ring

theorem cycW_eps (N : CircNetwork V) (ε : ℝ) (Γ : List V) :
    cycW (fun v w => N.c v w + ε) Γ = cycleCost N Γ + (Γ.length : ℝ) * ε := by
  unfold cycW cycleCost
  rw [List.sum_map_add]
  simp [cycleArcs_length]

theorem meanCost_ge_of_epsOpt (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) (p : V → ℝ)
    (hp : IsEpsOptimalWrt N f ε p) (Γ : List V) (hΓ : IsResidualCycle N f Γ) :
    -ε ≤ meanCost N Γ := by
  have hlen : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
  have hsum := cycle_reduced_sum N p Γ
  have hge := List.card_nsmul_le_sum ((cycleArcs Γ).map (fun a => reducedCost N p a.1 a.2)) (-ε)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hp a.1 a.2 (hΓ.2.2 a ha).1 (hΓ.2.2 a ha).2)
  rw [hsum, List.length_map, cycleArcs_length] at hge
  simp only [nsmul_eq_mul] at hge
  unfold meanCost
  rw [le_div_iff₀ hlen]
  linarith

theorem exists_price_eps (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ)
    (hcyc : ∀ Γ, IsResidualCycle N f Γ → -ε ≤ meanCost N Γ) :
    ∃ p, IsEpsOptimalWrt N f ε p := by
  have hneg : ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycW (fun v w => N.c v w + ε) Γ < 0 := by
    rintro ⟨Γ, hΓ, hlt⟩
    have hlen : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
    have h := hcyc Γ hΓ
    unfold meanCost at h
    rw [le_div_iff₀ hlen] at h
    rw [cycW_eps] at hlt
    linarith
  obtain ⟨p, hp⟩ := exists_pot_w N f _ hneg
  refine ⟨p, fun v w hvw hres => ?_⟩
  have := hp v w hvw hres
  unfold reducedCost
  linarith

theorem meanCost_neg (N : CircNetwork V) (Γ : List V) (hne : Γ ≠ []) (hneg : cycleCost N Γ < 0) :
    meanCost N Γ < 0 := by
  have hlen : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hne
  exact div_neg_of_neg_of_pos hneg hlen

theorem epsOpt_bdd (N : CircNetwork V) (f : V → V → ℝ) :
    BddBelow {ε : ℝ | IsEpsOptimal N f ε} := ⟨0, fun _ h => h.2.1⟩

theorem epsOpt_nonneg (N : CircNetwork V) (f : V → V → ℝ) : 0 ≤ epsOpt N f :=
  Real.sInf_nonneg (fun _ h => h.2.1)

/-- Theorem 3.3 core: for a circulation with a negative min-mean residual cycle `Γ`,
`f` is `(-μ)`-optimal and `ε(f) = -μ`. -/
theorem eps_core (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsMinMeanResidualCycle N f Γ) (hneg : cycleCost N Γ < 0) :
    IsEpsOptimal N f (-meanCost N Γ) ∧ epsOpt N f = -meanCost N Γ := by
  have hμ := meanCost_neg N Γ hΓ.1.1 hneg
  have hmem : IsEpsOptimal N f (-meanCost N Γ) := by
    refine ⟨hf, by linarith, exists_price_eps N f _ (fun Γ' hΓ' => ?_)⟩
    have := hΓ.2 Γ' hΓ'
    linarith
  refine ⟨hmem, ?_⟩
  apply IsLeast.csInf_eq
  refine ⟨hmem, fun ε hε => ?_⟩
  obtain ⟨-, -, p, hp⟩ := hε
  have := meanCost_ge_of_epsOpt N f ε p hp Γ hΓ.1
  linarith

theorem epsOpt_eq_of_core (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsMinMeanResidualCycle N f Γ) (hneg : cycleCost N Γ < 0) :
    epsOpt N f = -meanCost N Γ := (eps_core N f hf Γ hΓ hneg).2

/-- Lemma 3.5 core: canceling a min-mean negative cycle gives an `ε(f)`-optimal circulation. -/
theorem cancel_isEpsOptimal (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsMinMeanResidualCycle N f Γ) (hneg : cycleCost N Γ < 0) :
    IsEpsOptimal N (cancel N f Γ) (-meanCost N Γ) := by
  have hμ := meanCost_neg N Γ hΓ.1.1 hneg
  obtain ⟨⟨-, -, p, hp⟩, -⟩ := eps_core N f hf Γ hΓ hneg
  set ε := -meanCost N Γ with hε
  set L := cycleArcs Γ with hLdef
  have hlen : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1.1
  -- tightness: every arc of the cycle has reduced cost exactly -ε
  have hge : ∀ a ∈ L, 0 ≤ reducedCost N p a.1 a.2 + ε := by
    intro a ha
    have := hp a.1 a.2 (hΓ.1.2.2 a ha).1 (hΓ.1.2.2 a ha).2
    linarith
  have htight : ∀ a ∈ L, reducedCost N p a.1 a.2 = -ε := by
    intro a ha
    have hsum : (L.map (fun b => reducedCost N p b.1 b.2 + ε)).sum = 0 := by
      rw [List.sum_map_add, hLdef, cycle_reduced_sum]
      simp only [List.map_const', List.sum_replicate, cycleArcs_length, nsmul_eq_mul]
      have : cycleCost N Γ = meanCost N Γ * Γ.length := by
        unfold meanCost; field_simp
      rw [this, hε]; ring
    have hle := List.single_le_sum (l := L.map (fun b => reducedCost N p b.1 b.2 + ε))
      (by intro x hx; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact hge b hb)
      (reducedCost N p a.1 a.2 + ε) (List.mem_map_of_mem ha)
    have := hge a ha
    rw [hsum] at hle
    linarith
  refine ⟨cancel_isCirculation N f hf Γ hΓ.1, by linarith, p, ?_⟩
  intro v w hvw hres
  by_cases hr : 0 < resCap N f v w
  · exact hp v w hvw hr
  · have hcnt : resCap N (cancel N f Γ) v w = resCap N f v w - cycleCap N f Γ * dL L v w := by
      unfold resCap; rw [cancel_eq]; ring
    have hδ := cycleCap_pos N f Γ hΓ.1
    have hdl : dL L v w < 0 := by
      by_contra h
      push_neg at h
      have := mul_nonneg hδ.le h
      rw [hcnt] at hres
      push_neg at hr
      linarith
    rw [dL_eq_count] at hdl
    have hcw : 0 < L.count (w, v) := by
      by_contra h0
      have h00 : L.count (w, v) = 0 := by omega
      rw [h00, Nat.cast_zero] at hdl
      have : (0:ℝ) ≤ (L.count (v, w) : ℝ) := Nat.cast_nonneg _
      linarith
    have hmem : (w, v) ∈ L := List.count_pos_iff.mp hcw
    have h1 := htight (w, v) hmem
    have h2 := reducedCost_antisymm N p v w hvw
    simp only at h1
    linarith

/-! ## Part 4: Lemma 3.6 -/

theorem new_resid_rev_mem (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V)
    (hΓ : IsResidualCycle N f Γ) (v w : V)
    (h1 : ¬ 0 < resCap N f v w) (h2 : 0 < resCap N (cancel N f Γ) v w) :
    (w, v) ∈ cycleArcs Γ := by
  have hcnt : resCap N (cancel N f Γ) v w
      = resCap N f v w - cycleCap N f Γ * dL (cycleArcs Γ) v w := by
    unfold resCap; rw [cancel_eq]; ring
  have hδ := cycleCap_pos N f Γ hΓ
  have hdl : dL (cycleArcs Γ) v w < 0 := by
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg hδ.le h
    rw [hcnt] at h2
    rw [not_lt] at h1
    linarith
  rw [dL_eq_count] at hdl
  have hcw : 0 < (cycleArcs Γ).count (w, v) := by
    by_contra h0
    have h00 : (cycleArcs Γ).count (w, v) = 0 := by omega
    rw [h00, Nat.cast_zero] at hdl
    have := Nat.cast_nonneg (α := ℝ) ((cycleArcs Γ).count (v, w))
    linarith
  exact List.count_pos_iff.mp hcw

theorem admissible_cycle (N : CircNetwork V) (f : V → V → ℝ) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (p : V → ℝ) (hp : IsEpsOptimalWrt N f ε0 p) (Γ : List V) (hΓ : IsResidualCycle N f Γ)
    (hlen : Γ.length ≤ Fintype.card V)
    (hbig : (1 - 1 / (Fintype.card V : ℝ)) * ε0 < -meanCost N Γ) :
    ∀ a ∈ cycleArcs Γ, reducedCost N p a.1 a.2 < 0 := by
  intro a0 ha0
  by_contra hnn
  rw [not_lt] at hnn
  have hl : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
  have hlle : (Γ.length : ℝ) ≤ Fintype.card V := by exact_mod_cast hlen
  have hn : (0:ℝ) < Fintype.card V := lt_of_lt_of_le hl hlle
  set L := cycleArcs Γ with hLdef
  have hge : ∀ a ∈ L, 0 ≤ reducedCost N p a.1 a.2 + ε0 := by
    intro a ha
    have := hp a.1 a.2 (hΓ.2.2 a ha).1 (hΓ.2.2 a ha).2
    linarith
  have hsum : (L.map (fun b => reducedCost N p b.1 b.2 + ε0)).sum
      = cycleCost N Γ + (Γ.length : ℝ) * ε0 := by
    rw [List.sum_map_add, hLdef, cycle_reduced_sum]
    simp only [List.map_const', List.sum_replicate, cycleArcs_length, nsmul_eq_mul]
  have hle := List.single_le_sum (l := L.map (fun b => reducedCost N p b.1 b.2 + ε0))
    (by intro x hx; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact hge b hb)
    (reducedCost N p a0.1 a0.2 + ε0) (List.mem_map_of_mem ha0)
  rw [hsum] at hle
  have hcost : cycleCost N Γ = meanCost N Γ * Γ.length := by
    unfold meanCost; field_simp
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set d := ε0 + meanCost N Γ with hd
  have h1 : ε0 ≤ (Γ.length : ℝ) * d := by
    rw [hd]; rw [hcost] at hle; nlinarith
  have h2 : (n - 1) * ε0 < n * (-meanCost N Γ) := by
    have e : n * ((1 - 1 / n) * ε0) = (n - 1) * ε0 := by field_simp
    have := mul_lt_mul_of_pos_left hbig hn
    rw [e] at this
    exact this
  have h3 : n * d < ε0 := by rw [hd]; nlinarith
  rcases lt_or_ge d 0 with hdn | hdp
  · nlinarith
  · have : (Γ.length : ℝ) * d ≤ n * d := mul_le_mul_of_nonneg_right hlle hdp
    linarith

theorem cancel_epsWrt (N : CircNetwork V) (f : V → V → ℝ) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (p : V → ℝ) (hp : IsEpsOptimalWrt N f ε0 p) (Γ : List V) (hΓ : IsResidualCycle N f Γ)
    (hadm : ∀ a ∈ cycleArcs Γ, reducedCost N p a.1 a.2 < 0) :
    IsEpsOptimalWrt N (cancel N f Γ) ε0 p := by
  intro v w hvw hres
  by_cases hr : 0 < resCap N f v w
  · exact hp v w hvw hr
  · have hm := new_resid_rev_mem N f Γ hΓ v w hr hres
    have h1 := hadm (w, v) hm
    have h2 := reducedCost_antisymm N p v w hvw
    simp only at h1
    linarith

theorem bottleneck (N : CircNetwork V) (f : V → V → ℝ) (p : V → ℝ) (Γ : List V)
    (hΓ : IsResidualCycle N f Γ)
    (hadm : ∀ a ∈ cycleArcs Γ, reducedCost N p a.1 a.2 < 0) :
    ∃ a ∈ cycleArcs Γ, ¬ 0 < resCap N (cancel N f Γ) a.1 a.2 := by
  obtain ⟨-, a, ha, hae⟩ := cycleCap_spec N f Γ (cycleArcs_ne_nil hΓ.1)
  refine ⟨a, ha, ?_⟩
  have hδ := cycleCap_pos N f Γ hΓ
  have hcnt : resCap N (cancel N f Γ) a.1 a.2
      = resCap N f a.1 a.2 - cycleCap N f Γ * dL (cycleArcs Γ) a.1 a.2 := by
    unfold resCap; rw [cancel_eq]; ring
  have hrev : (a.2, a.1) ∉ cycleArcs Γ := by
    intro hm
    have h1 := hadm _ hm
    have h2 := hadm a ha
    have h3 := reducedCost_antisymm N p a.1 a.2 (hΓ.2.2 a ha).1
    simp only at h1
    linarith
  have hdl : 1 ≤ dL (cycleArcs Γ) a.1 a.2 := by
    rw [dL_eq_count]
    have c1 : 1 ≤ (cycleArcs Γ).count (a.1, a.2) := List.count_pos_iff.mpr (by simpa using ha)
    have c2 : (cycleArcs Γ).count (a.2, a.1) = 0 := List.count_eq_zero.mpr hrev
    rw [c2, Nat.cast_zero]
    have : (1:ℝ) ≤ ((cycleArcs Γ).count (a.1, a.2) : ℝ) := by exact_mod_cast c1
    linarith
  rw [hcnt, ← hae]
  nlinarith


/-! ## Part 5: Lemma 3.6 main -/

theorem lemma36 (N : CircNetwork V) (F : ℕ → V → V → ℝ) (hrun : IsMinMeanRun N F N.E.card) :
    epsOpt N (F N.E.card) ≤ (1 - 1 / (Fintype.card V : ℝ)) * epsOpt N (F 0) := by
  classical
  set m := N.E.card with hm
  have hcirc : ∀ i, i ≤ m → IsCirculation N (F i) := fun i hi => run_isCirculation N F m hrun i hi
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · have hE : N.E = ∅ := Finset.card_eq_zero.mp h0
    have h0mem : IsEpsOptimal N (F 0) 0 :=
      ⟨hrun.1, le_rfl, fun _ => 0, fun v w hvw => by rw [hE] at hvw; simp at hvw⟩
    have : epsOpt N (F 0) = 0 :=
      le_antisymm (csInf_le (epsOpt_bdd N _) h0mem) (epsOpt_nonneg N _)
    rw [h0, this]; simp
  choose! Γ hΓ using fun (i : ℕ) (hi : i < m) => hrun.2 i hi
  have hε : ∀ i < m, epsOpt N (F i) = -meanCost N (Γ i) := fun i hi =>
    epsOpt_eq_of_core N (F i) (hcirc i hi.le) (Γ i) (hΓ i hi).1 (hΓ i hi).2.1
  have hmono_step : ∀ i < m, epsOpt N (F (i + 1)) ≤ epsOpt N (F i) := by
    intro i hi
    have h := cancel_isEpsOptimal N (F i) (hcirc i hi.le) (Γ i) (hΓ i hi).1 (hΓ i hi).2.1
    rw [← (hΓ i hi).2.2] at h
    rw [hε i hi]
    exact csInf_le (epsOpt_bdd N _) h
  have hmono : ∀ j i, i ≤ j → j ≤ m → epsOpt N (F j) ≤ epsOpt N (F i) := by
    intro j
    induction j with
    | zero => intro i hi _; have : i = 0 := by omega
              subst this; exact le_rfl
    | succ j ih =>
      intro i hi hj
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [h]
      · exact (hmono_step j (by omega)).trans (ih i (by omega) (by omega))
  obtain ⟨⟨-, -, p, hp0'⟩, -⟩ := eps_core N (F 0) (hcirc 0 (by omega)) (Γ 0) (hΓ 0 hpos).1
    (hΓ 0 hpos).2.1
  set ε0 := epsOpt N (F 0) with hε0def
  have hp0 : IsEpsOptimalWrt N (F 0) ε0 p := by rw [hε0def, hε 0 hpos]; exact hp0'
  have hε0 : 0 ≤ ε0 := epsOpt_nonneg N _
  by_contra hcon
  have H : ∀ i < m, (1 - 1 / (Fintype.card V : ℝ)) * ε0 < epsOpt N (F i) := by
    intro i hi
    by_contra h
    exact hcon ((hmono m i hi.le le_rfl).trans (not_lt.mp h))
  have hadm_all : ∀ i < m, IsEpsOptimalWrt N (F i) ε0 p →
      ∀ a ∈ cycleArcs (Γ i), reducedCost N p a.1 a.2 < 0 := by
    intro i hi hpi
    refine admissible_cycle N (F i) ε0 hε0 p hpi (Γ i) (hΓ i hi).1.1 ?_ ?_
    · exact (hΓ i hi).1.1.2.1.length_le_card
    · have := H i hi
      rw [hε i hi] at this
      exact this
  let A : ℕ → Finset (V × V) := fun i =>
    N.E.filter (fun a => 0 < resCap N (F i) a.1 a.2 ∧ reducedCost N p a.1 a.2 < 0)
  have key : ∀ i, i ≤ m → IsEpsOptimalWrt N (F i) ε0 p ∧ (A i).card + i ≤ (A 0).card := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hp0, by simp⟩
    | succ i ih =>
      intro hi
      have hi' : i < m := by omega
      obtain ⟨ihp, ihc⟩ := ih hi'.le
      have hadm := hadm_all i hi' ihp
      have hF : F (i + 1) = cancel N (F i) (Γ i) := (hΓ i hi').2.2
      have hres := (hΓ i hi').1.1
      refine ⟨?_, ?_⟩
      · rw [hF]; exact cancel_epsWrt N (F i) ε0 hε0 p ihp (Γ i) hres hadm
      · obtain ⟨a, ha, hna⟩ := bottleneck N (F i) p (Γ i) hres hadm
        have haA : a ∈ A i := by
          simp only [A, Finset.mem_filter]
          exact ⟨(hres.2.2 a ha).1, (hres.2.2 a ha).2, hadm a ha⟩
        have hsub : A (i + 1) ⊆ (A i).erase a := by
          intro b hb
          simp only [A, Finset.mem_filter] at hb
          obtain ⟨hbE, hbr, hbc⟩ := hb
          rw [hF] at hbr
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · rintro rfl; exact hna hbr
          · simp only [A, Finset.mem_filter]
            refine ⟨hbE, ?_, hbc⟩
            by_contra hnr
            have hm' := new_resid_rev_mem N (F i) (Γ i) hres b.1 b.2 hnr hbr
            have h1 := hadm _ hm'
            have h2 := reducedCost_antisymm N p b.1 b.2 hbE
            simp only at h1
            linarith
        have := Finset.card_le_card hsub
        have h2 := Finset.card_erase_add_one haA
        omega
  -- (A 0).card < m
  have hA0 : (A 0).card < m := by
    rcases (A 0).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · rw [h]; simpa using hpos
    · simp only [A, Finset.mem_filter] at ha
      obtain ⟨haE, -, hac⟩ := ha
      have hrevE : (a.2, a.1) ∈ N.E := (N.symm a.1 a.2).mp haE
      have hrevn : (a.2, a.1) ∉ A 0 := by
        simp only [A, Finset.mem_filter]
        have := reducedCost_antisymm N p a.1 a.2 haE
        rintro ⟨-, -, h⟩
        linarith
      have hss : A 0 ⊂ N.E := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨_, hrevE, hrevn⟩
      exact Finset.card_lt_card hss
  obtain ⟨hpi, hci⟩ := key (A 0).card hA0.le
  have hadm := hadm_all (A 0).card hA0 hpi
  have hne := cycleArcs_ne_nil (hΓ (A 0).card hA0).1.1.1
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  have hres := (hΓ (A 0).card hA0).1.1
  have haA : a ∈ A (A 0).card := by
    simp only [A, Finset.mem_filter]
    exact ⟨(hres.2.2 a ha).1, (hres.2.2 a ha).2, hadm a ha⟩
  have : 0 < (A (A 0).card).card := Finset.card_pos.mpr ⟨a, haA⟩
  omega


/-! ## Part 6a: Theorem 3.8 (copied from our proof of 932da085) -/

namespace CC932


open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Layers of vertices reachable from `w` along arcs with `h > 0`. -/
noncomputable def layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) : ℕ → Finset V
  | 0 => {w}
  | k + 1 => layer N h w k ∪
      Finset.univ.filter (fun y => ∃ x ∈ layer N h w k, (x, y) ∈ N.E ∧ 0 < h x y)

lemma layer_succ_sub (N : CircNetwork V) (h : V → V → ℝ) (w : V) (k : ℕ) :
    layer N h w k ⊆ layer N h w (k + 1) := by
  show layer N h w k ⊆ layer N h w k ∪ _
  exact Finset.subset_union_left

lemma w_mem_layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∀ k : ℕ, w ∈ layer N h w k := by
  intro k
  induction k with
  | zero => simp [layer]
  | succ k ih => exact layer_succ_sub N h w k ih

lemma layer_bound (N : CircNetwork V) (h : V → V → ℝ) (w : V) (q : V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε) :
    ∀ k : ℕ, ∀ x ∈ layer N h w k, q x ≤ q w + 2 * (k : ℝ) * ε := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp [layer] at hx
    subst hx
    simp
  | succ k ih =>
    intro x hx
    have hx' : x ∈ layer N h w k ∪
        Finset.univ.filter (fun y => ∃ z ∈ layer N h w k, (z, y) ∈ N.E ∧ 0 < h z y) := hx
    rcases Finset.mem_union.mp hx' with h1 | h1
    · have := ih x h1
      push_cast
      nlinarith
    · obtain ⟨z, hz, hzE, hzpos⟩ := (Finset.mem_filter.mp h1).2
      have := ih z hz
      have := hstep z x hzE hzpos
      push_cast
      nlinarith

lemma layer_stab (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∃ k : ℕ, k + 1 ≤ Fintype.card V ∧ layer N h w (k + 1) ⊆ layer N h w k := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, k ≤ Fintype.card V → k + 1 ≤ (layer N h w k).card := by
    intro k
    induction k with
    | zero => intro _; simp [layer]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hss : layer N h w k ⊂ layer N h w (k + 1) :=
        HasSubset.Subset.ssubset_of_not_subset (layer_succ_sub N h w k) (hcon k hk)
      have := Finset.card_lt_card hss
      omega
  have := key (Fintype.card V) le_rfl
  have := Finset.card_le_univ (layer N h w (Fintype.card V))
  omega

lemma cut_false (N : CircNetwork V) (h : V → V → ℝ) (S : Finset V)
    (hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a)
    (hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0)
    (hclosed : ∀ a ∈ S, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ S)
    (v w : V) (hw : w ∈ S) (hv : v ∉ S) (hvw : (v, w) ∈ N.E) (hpos : 0 < h v w) : False := by
  classical
  let φ : V → V → ℝ := fun x y => if (x, y) ∈ N.E then h y x else 0
  have hφanti : ∀ x y, φ x y = -φ y x := by
    intro x y
    simp only [φ]
    by_cases hxy : (x, y) ∈ N.E
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      rw [if_pos hxy, if_pos hyx]
      exact hanti y x hyx
    · have hyx : (y, x) ∉ N.E := fun h' => hxy ((N.symm y x).1 h')
      rw [if_neg hxy, if_neg hyx]
      simp
  have htot : ∑ x ∈ S, ∑ y, φ x y = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hcons x, Finset.sum_filter]
  have hA : ∑ x ∈ S, ∑ y ∈ S, φ x y = 0 := by
    have h1 : ∑ x ∈ S, ∑ y ∈ S, φ x y = ∑ y ∈ S, ∑ x ∈ S, φ x y := Finset.sum_comm
    have h2 : ∑ y ∈ S, ∑ x ∈ S, φ x y = -∑ y ∈ S, ∑ x ∈ S, φ y x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hφanti x y
    linarith
  have hnn : ∀ x ∈ S, ∀ y ∈ Sᶜ, 0 ≤ φ x y := by
    intro x hx y hy
    simp only [φ]
    split_ifs with hxy
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      have hle : ¬ 0 < h x y := fun hp => (Finset.mem_compl.mp hy) (hclosed x hx y hxy hp)
      push_neg at hle
      rw [hanti y x hyx]
      linarith
    · exact le_rfl
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  have hB : 0 < ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    have hv' : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    have e1 : φ w v ≤ ∑ y ∈ Sᶜ, φ w y :=
      Finset.single_le_sum (fun y hy => hnn w hw y hy) hv'
    have e2 : ∑ y ∈ Sᶜ, φ w y ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y :=
      Finset.single_le_sum (f := fun x => ∑ y ∈ Sᶜ, φ x y)
        (fun x hx => Finset.sum_nonneg (fun y hy => hnn x hx y hy)) hw
    have e0 : φ w v = h v w := by simp only [φ]; rw [if_pos hwv]
    linarith
  have hsplit : ∑ x ∈ S, ∑ y, φ x y =
      ∑ x ∈ S, ∑ y ∈ S, φ x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_add_sum_compl]
  linarith

lemma main (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε) (f : V → V → ℝ)
    (hf : IsCirculation N f) (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V)
    (hvw : (v, w) ∈ N.E)
    (hneg : reducedCost N p v w ≤ -(2 * (Fintype.card V : ℝ) * ε))
    (g : V → V → ℝ) (hg : IsEpsOptimal N g ε) : g v w = f v w := by
  obtain ⟨hgc, -, p', hgp⟩ := hg
  haveI : Nonempty V := ⟨v⟩
  have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hfu : N.u v w ≤ f v w := by
    by_contra hlt
    push_neg at hlt
    have := hfp v w hvw (by unfold resCap; linarith)
    nlinarith
  by_contra hne
  have hlt : g v w < f v w := lt_of_le_of_ne (le_trans (hgc.1 v w hvw) hfu) hne
  let h : V → V → ℝ := fun a b => f a b - g a b
  let q : V → ℝ := fun x => p' x - p x
  have hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε := by
    intro a b hab hpos
    have hba := (N.symm a b).1 hab
    simp only [h] at hpos
    have h1 := hgp a b hab (by unfold resCap; linarith [hf.1 a b hab])
    have h2 := hfp b a hba (by
      unfold resCap
      linarith [hf.2.1 a b hab, hgc.2.1 a b hab, hgc.1 b a hba])
    have h3 := N.cost_antisymm a b hab
    unfold reducedCost at h1 h2
    simp only [q]
    linarith
  have hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a := by
    intro a b hab
    simp only [h]
    rw [hf.2.1 a b hab, hgc.2.1 a b hab]
    ring
  have hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0 := by
    intro x
    simp only [h]
    rw [Finset.sum_sub_distrib, hf.2.2 x, hgc.2.2 x]
    ring
  obtain ⟨k, hk, hsub⟩ := layer_stab N h w
  have hclosed : ∀ a ∈ layer N h w k, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ layer N h w k := by
    intro a ha b hab hp
    apply hsub
    show b ∈ layer N h w k ∪ _
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, hab, hp⟩
  have hwS : w ∈ layer N h w k := w_mem_layer N h w k
  have hvS : v ∈ layer N h w k := by
    by_contra hvS
    exact cut_false N h (layer N h w k) hanti hcons hclosed v w hwS hvS hvw
      (by simp only [h]; linarith)
  have hqv := layer_bound N h w q ε hε.le hstep k v hvS
  have hg1 := hgp v w hvw (by unfold resCap; linarith [hf.1 v w hvw])
  have hkR : ((k : ℝ) + 1) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hk
  have hkε : (k : ℝ) * ε ≤ ((Fintype.card V : ℝ) - 1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  unfold reducedCost at hneg hg1
  simp only [q] at hqv
  nlinarith


end CC932

theorem eps_fixed {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε) (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V) (hvw : (v, w) ∈ N.E)
    (hbig : 2 * (Fintype.card V : ℝ) * ε ≤ |reducedCost N p v w|) :
    IsEpsFixed N ε v w := by
  intro g g' hg hg'
  rcases le_abs'.mp hbig with hneg | hpos
  · rw [CC932.main N ε hε f hf p hfp v w hvw hneg g hg,
      CC932.main N ε hε f hf p hfp v w hvw hneg g' hg']
  · have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
    have hneg' : reducedCost N p w v ≤ -(2 * (Fintype.card V : ℝ) * ε) := by
      have := N.cost_antisymm v w hvw
      unfold reducedCost at hpos ⊢
      linarith
    have e1 := CC932.main N ε hε f hf p hfp w v hwv hneg' g hg
    have e2 := CC932.main N ε hε f hf p hfp w v hwv hneg' g' hg'
    rw [hg.1.2.1 v w hvw, hg'.1.2.1 v w hvw, e1, e2]


/-! ## Part 6b: run helpers, cycle shape, exponential bound -/

theorem run_step_le (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ)
    (hrun : IsMinMeanRun N F K) (i : ℕ) (hi : i < K) :
    epsOpt N (F (i + 1)) ≤ epsOpt N (F i) := by
  obtain ⟨Γ, hΓ, hneg, hF⟩ := hrun.2 i hi
  have hc := run_isCirculation N F K hrun i hi.le
  have h := cancel_isEpsOptimal N (F i) hc Γ hΓ hneg
  rw [← hF] at h
  rw [epsOpt_eq_of_core N (F i) hc Γ hΓ hneg]
  exact csInf_le (epsOpt_bdd N _) h

theorem run_eps_mono (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ)
    (hrun : IsMinMeanRun N F K) :
    ∀ j i, i ≤ j → j ≤ K → epsOpt N (F j) ≤ epsOpt N (F i) := by
  intro j
  induction j with
  | zero =>
    intro i hi _
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with h | h
    · rw [h]
    · exact (run_step_le N F K hrun j (by omega)).trans (ih i (by omega) (by omega))

theorem run_mem (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ)
    (hrun : IsMinMeanRun N F K) (hK : 0 < K) (l : ℕ) (hl : l ≤ K) :
    ∃ ε, IsEpsOptimal N (F l) ε := by
  rcases Nat.lt_or_ge l K with h | h
  · obtain ⟨Γ, hΓ, hneg, -⟩ := hrun.2 l h
    exact ⟨_, (eps_core N (F l) (run_isCirculation N F K hrun l hl) Γ hΓ hneg).1⟩
  · have hlK : l = K := by omega
    subst hlK
    obtain ⟨Γ, hΓ, hneg, hF⟩ := hrun.2 (l - 1) (by omega)
    have hK' : l - 1 + 1 = l := by omega
    rw [hK'] at hF
    rw [hF]
    exact ⟨_, cancel_isEpsOptimal N (F (l - 1)) (run_isCirculation N F l hrun (l - 1) (by omega))
      Γ hΓ hneg⟩

theorem isEpsOptimal_mono (N : CircNetwork V) (f : V → V → ℝ) (s t : ℝ)
    (h : IsEpsOptimal N f s) (hst : s ≤ t) : IsEpsOptimal N f t := by
  obtain ⟨hf, hs, p, hp⟩ := h
  exact ⟨hf, hs.trans hst, p, fun v w hvw hr => by have := hp v w hvw hr; linarith⟩

theorem isEpsOptimal_of_epsOpt_lt (N : CircNetwork V) (f : V → V → ℝ)
    (hne : ∃ ε, IsEpsOptimal N f ε) (t : ℝ) (h : epsOpt N f < t) : IsEpsOptimal N f t := by
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt (s := {ε : ℝ | IsEpsOptimal N f ε}) hne h
  exact isEpsOptimal_mono N f s t hs hst.le

theorem three_le_length (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V)
    (hΓ : IsResidualCycle N f Γ) (hneg : cycleCost N Γ < 0) : 3 ≤ Γ.length := by
  rcases Γ with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · exact absurd rfl hΓ.1
  · exfalso
    have hxx : (x, x) ∈ cycleArcs [x] := by simp [cycleArcs]
    have hE := (hΓ.2.2 _ hxx).1
    have h1 := N.cost_antisymm x x hE
    have : cycleCost N [x] = N.c x x := by simp [cycleCost, cycleArcs]
    rw [this] at hneg
    linarith
  · exfalso
    have hxy : (x, y) ∈ cycleArcs [x, y] := by simp [cycleArcs]
    have hE := (hΓ.2.2 _ hxy).1
    have h1 := N.cost_antisymm x y hE
    have : cycleCost N [x, y] = N.c x y + N.c y x := by simp [cycleCost, cycleArcs]
    rw [this] at hneg
    linarith
  · simp

theorem rev_not_mem {Γ : List V} (hnd : Γ.Nodup) (h3 : 3 ≤ Γ.length) {v w : V}
    (h : (v, w) ∈ cycleArcs Γ) : (w, v) ∉ cycleArcs Γ := by
  intro h'
  unfold cycleArcs at h h'
  obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp h
  obtain ⟨k', hk', hkv'⟩ := List.mem_iff_getElem.mp h'
  rw [List.getElem_zip] at hkv hkv'
  simp only [Prod.mk.injEq, List.getElem_rotate] at hkv hkv'
  have hkl : k < Γ.length := by simpa using hk
  have hkl' : k' < Γ.length := by simpa using hk'
  obtain ⟨a1, a2⟩ := hkv
  obtain ⟨b1, b2⟩ := hkv'
  have e1 : (k + 1) % Γ.length = k' := by
    have := (List.Nodup.getElem_inj_iff hnd).mp (a2.trans b1.symm)
    exact this
  have e2 : (k' + 1) % Γ.length = k := by
    have := (List.Nodup.getElem_inj_iff hnd).mp (b2.trans a1.symm)
    exact this
  set l := Γ.length with hl
  rcases Nat.lt_or_ge (k + 1) l with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at e1
    subst e1
    rcases Nat.lt_or_ge (k + 1 + 1) l with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at e2; omega
    · have : k + 1 + 1 = l := by omega
      rw [this, Nat.mod_self] at e2
      omega
  · have : k + 1 = l := by omega
    rw [this, Nat.mod_self] at e1
    subst e1
    rw [Nat.mod_eq_of_lt (by omega)] at e2
    omega

theorem pow_lt_inv (n : ℕ) (hn : 2 ≤ n) :
    (1 - 1 / (n : ℝ)) ^ (n * ⌈Real.log n + 1⌉₊) < 1 / (2 * n) := by
  have hx : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0:ℝ) < n := by linarith
  set C := ⌈Real.log n + 1⌉₊ with hC
  have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n:ℝ) ≤ 1 := by rw [div_le_one hx0]; linarith
    linarith
  have h1 : 1 - 1 / (n : ℝ) ≤ Real.exp (-1 / n) := by
    have := Real.add_one_le_exp (-1 / (n:ℝ))
    have e : -1 / (n:ℝ) = -(1 / n) := by ring
    rw [e] at this ⊢
    linarith
  have h2 := pow_le_pow_left₀ h0 h1 (n * C)
  have h3 : Real.exp (-1 / n) ^ (n * C) = Real.exp (-(C : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have h4 : Real.exp (-(C : ℝ)) ≤ Real.exp (-(Real.log n + 1)) := by
    apply Real.exp_le_exp.mpr
    have : Real.log n + 1 ≤ (C : ℝ) := Nat.le_ceil _
    linarith
  have h5 : Real.exp (-(Real.log n + 1)) = (1 / (n : ℝ)) * Real.exp (-1) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hx0]
    simp
  have h6 : Real.exp (-1) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg]
    have h2 : (2:ℝ) < Real.exp 1 := by linarith
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using h2
  calc (1 - 1 / (n : ℝ)) ^ (n * C) ≤ Real.exp (-1 / n) ^ (n * C) := h2
    _ = Real.exp (-(C : ℝ)) := h3
    _ ≤ Real.exp (-(Real.log n + 1)) := h4
    _ = (1 / (n : ℝ)) * Real.exp (-1) := h5
    _ < (1 / (n : ℝ)) * (1 / 2) := by
        apply mul_lt_mul_of_pos_left h6
        positivity
    _ = 1 / (2 * n) := by field_simp


/-! ## Part 7: blocks (N2), group fixes an arc (N3), counting -/

theorem lemma36_shift (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ)
    (hrun : IsMinMeanRun N F K) (j : ℕ) (hj : j + N.E.card ≤ K) :
    epsOpt N (F (j + N.E.card)) ≤ (1 - 1 / (Fintype.card V : ℝ)) * epsOpt N (F j) := by
  have := lemma36 N (fun t => F (j + t))
    ⟨run_isCirculation N F K hrun j (by omega), fun t ht => hrun.2 (j + t) (by omega)⟩
  exact this

theorem epsOpt_blocks_le (N : CircNetwork V) (hn : 2 ≤ Fintype.card V)
    (F : ℕ → V → V → ℝ) (K : ℕ) (hrun : IsMinMeanRun N F K) (i q : ℕ)
    (hiq : i + N.E.card * q ≤ K) :
    epsOpt N (F (i + N.E.card * q)) ≤ (1 - 1 / (Fintype.card V : ℝ)) ^ q * epsOpt N (F i) := by
  have hx : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have h0 : 0 ≤ 1 - 1 / (Fintype.card V : ℝ) := by
    have : 1 / (Fintype.card V : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  induction q with
  | zero => simp
  | succ q ih =>
    have hq : i + N.E.card * q ≤ K := by
      have : N.E.card * q ≤ N.E.card * (q + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have e : i + N.E.card * (q + 1) = (i + N.E.card * q) + N.E.card := by ring
    have hs : (i + N.E.card * q) + N.E.card ≤ K := by rw [← e]; exact hiq
    rw [e]
    calc epsOpt N (F ((i + N.E.card * q) + N.E.card))
        ≤ (1 - 1 / (Fintype.card V : ℝ)) * epsOpt N (F (i + N.E.card * q)) :=
          lemma36_shift N F K hrun _ hs
      _ ≤ (1 - 1 / (Fintype.card V : ℝ)) * ((1 - 1 / (Fintype.card V : ℝ)) ^ q * epsOpt N (F i)) :=
          mul_le_mul_of_nonneg_left (ih hq) h0
      _ = (1 - 1 / (Fintype.card V : ℝ)) ^ (q + 1) * epsOpt N (F i) := by ring

theorem group_fixes_arc (N : CircNetwork V) (hn : 2 ≤ Fintype.card V)
    (F : ℕ → V → V → ℝ) (K : ℕ) (hrun : IsMinMeanRun N F K) (i : ℕ)
    (hiK : i + N.E.card * (Fintype.card V * ⌈Real.log (Fintype.card V) + 1⌉₊) ≤ K)
    (hi : i < K) :
    ∃ v w, (v, w) ∈ N.E ∧ v ≠ w ∧ F (i + 1) v w ≠ F i v w ∧
      ∀ l, i + N.E.card * (Fintype.card V * ⌈Real.log (Fintype.card V) + 1⌉₊) ≤ l → l ≤ K →
        F l v w = F (i + N.E.card * (Fintype.card V * ⌈Real.log (Fintype.card V) + 1⌉₊)) v w := by
  classical
  set n := Fintype.card V with hndef
  set C := ⌈Real.log n + 1⌉₊ with hC
  set j := i + N.E.card * (n * C) with hj
  obtain ⟨Γ, hΓ, hneg, hF⟩ := hrun.2 i hi
  have hci := run_isCirculation N F K hrun i hi.le
  have hres : IsResidualCycle N (F i) Γ := hΓ.1
  have heps := epsOpt_eq_of_core N (F i) hci Γ hΓ hneg
  have hμ := meanCost_neg N Γ hres.1 hneg
  set ε := epsOpt N (F i) with hεdef
  have hεpos : 0 < ε := by rw [heps]; linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2 := epsOpt_blocks_le N hn F K hrun i (n * C) hiK
  have h3 := pow_lt_inv n hn
  set ε'' := ε / (2 * n) with hε''
  have hε''pos : 0 < ε'' := by positivity
  have hlt : epsOpt N (F j) < ε'' := by
    calc epsOpt N (F j) ≤ (1 - 1 / (n : ℝ)) ^ (n * C) * ε := h2
      _ < (1 / (2 * (n : ℝ))) * ε := mul_lt_mul_of_pos_right h3 hεpos
      _ = ε'' := by rw [hε'']; field_simp
  have hjK : j ≤ K := hiK
  have hopt : ∀ l, j ≤ l → l ≤ K → IsEpsOptimal N (F l) ε'' := fun l hjl hlK =>
    isEpsOptimal_of_epsOpt_lt N _ (run_mem N F K hrun (by omega) l hlK) _
      (lt_of_le_of_lt (run_eps_mono N F K hrun l j hjl hlK) hlt)
  obtain ⟨-, -, p, hp⟩ := hopt j le_rfl hjK
  have hL : ∃ a ∈ cycleArcs Γ, reducedCost N p a.1 a.2 ≤ -ε := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < ((cycleArcs Γ).map (fun b => reducedCost N p b.1 b.2 + ε)).sum := by
      apply List.sum_pos
      · intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have := hcon b hb
        linarith
      · simpa using cycleArcs_ne_nil hres.1
    have hsum : ((cycleArcs Γ).map (fun b => reducedCost N p b.1 b.2 + ε)).sum
        = cycleCost N Γ + (Γ.length : ℝ) * ε := by
      rw [List.sum_map_add, cycle_reduced_sum]
      simp only [List.map_const', List.sum_replicate, cycleArcs_length, nsmul_eq_mul]
    have hlen : (0:ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hres.1
    have hcost : cycleCost N Γ = meanCost N Γ * Γ.length := by
      unfold meanCost; field_simp
    rw [hsum, hcost, heps] at hpos
    linarith
  obtain ⟨⟨v, w⟩, hvwL, hrc⟩ := hL
  have hvwE : (v, w) ∈ N.E := (hres.2.2 _ hvwL).1
  have hbig : 2 * (n : ℝ) * ε'' ≤ |reducedCost N p v w| := by
    have : 2 * (n : ℝ) * ε'' = ε := by rw [hε'']; field_simp
    rw [this]
    simp only at hrc
    have := neg_le_abs (reducedCost N p v w)
    linarith
  have hfix := eps_fixed N ε'' hε''pos (F j) (hopt j le_rfl hjK).1 p hp v w hvwE hbig
  have h3l := three_le_length N (F i) Γ hres hneg
  have hrev := rev_not_mem hres.2.1 h3l hvwL
  refine ⟨v, w, hvwE, ?_, ?_, ?_⟩
  · rintro rfl; exact hrev hvwL
  · rw [hF, cancel_eq, dL_eq_count]
    have c1 : (cycleArcs Γ).count (v, w) = 1 :=
      List.count_eq_one_of_mem (cycleArcs_nodup hres.2.1) hvwL
    have c2 : (cycleArcs Γ).count (w, v) = 0 := List.count_eq_zero.mpr hrev
    rw [c1, c2]
    have := cycleCap_pos N (F i) Γ hres
    intro h
    simp at h
    linarith
  · intro l hjl hlK
    exact hfix _ _ (hopt l hjl hlK) (hopt j le_rfl hjK)


/-! ## Part 8: the counting argument -/

theorem parent (N : CircNetwork V) (hn : 2 ≤ Fintype.card V)
    (F : ℕ → V → V → ℝ) (K : ℕ) (hrun : IsMinMeanRun N F K) :
    K ≤ Fintype.card V * N.E.card ^ 2 * ⌈Real.log (Fintype.card V) + 1⌉₊ := by
  classical
  by_contra hK
  rw [not_le] at hK
  set n := Fintype.card V with hndef
  set C := ⌈Real.log n + 1⌉₊ with hC
  set m := N.E.card with hm
  have hbound : n * m ^ 2 * C = m * (m * (n * C)) := by ring
  rw [hbound] at hK
  obtain ⟨k, hk⟩ : ∃ k, k = m * (n * C) := ⟨_, rfl⟩
  rw [← hk] at hK
  have hCpos : 1 ≤ C := by
    rw [hC]
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.pos_iff_ne_zero.mp
    apply Nat.ceil_pos.mpr
    have : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have := Real.log_nonneg this
    linarith
  rcases Nat.eq_zero_or_pos m with h0 | hmpos
  · have hK0 : 0 < K := by rw [h0] at hK; simpa using hK
    have hE : N.E = ∅ := Finset.card_eq_zero.mp h0
    obtain ⟨v, w, hvw, -⟩ := group_fixes_arc N hn F K hrun 0
      (by rw [← hm, h0]; simp) hK0
    rw [hE] at hvw
    simp at hvw
  have hkpos : 1 ≤ k := by
    rw [hk]; exact Nat.mul_pos hmpos (Nat.mul_pos (by omega) hCpos)
  have h1 : ∀ g, g < m → g * k + k ≤ m * k := by
    intro g hg
    calc g * k + k = (g + 1) * k := by ring
      _ ≤ m * k := Nat.mul_le_mul_right k hg
  have hiK : ∀ g, g < m → g * k + N.E.card * (n * C) ≤ K := by
    intro g hg
    have e : N.E.card * (n * C) = k := by rw [hk]
    rw [e]; exact (h1 g hg).trans hK.le
  have hi : ∀ g, g < m → g * k < K := fun g hg =>
    lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (h1 g hg)) hK
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  choose! v w hvw using fun (g : ℕ) (hg : g < m) =>
    group_fixes_arc N hn F K hrun (g * k) (hiK g hg) (hi g hg)
  have hconst0 : ∀ g, g < m → ∀ l, g * k + k ≤ l → l ≤ K →
      F l (v g) (w g) = F (g * k + k) (v g) (w g) := by
    intro g hg l hl1 hl2
    have e : N.E.card * (n * C) = k := by rw [hk]
    have := (hvw g hg).2.2.2 l (by rw [e]; exact hl1) hl2
    rw [e] at this
    exact this
  have hanti : ∀ l, l ≤ K → ∀ a b, (a, b) ∈ N.E → F l a b = - F l b a :=
    fun l hl a b h => (run_isCirculation N F K hrun l hl).2.1 a b h
  have hrevE : ∀ g, g < m → (w g, v g) ∈ N.E := fun g hg => (N.symm _ _).mp (hvw g hg).1
  let φ : ℕ × Bool → V × V := fun x => if x.2 then (v x.1, w x.1) else (w x.1, v x.1)
  have hφE : ∀ g, g < m → ∀ b, φ (g, b) ∈ N.E := by
    intro g hg b
    cases b
    · simp only [φ]; exact hrevE g hg
    · simp only [φ]; exact (hvw g hg).1
  have hleK : ∀ g, g < m → g * k + k ≤ K := fun g hg => (h1 g hg).trans hK.le
  have hchg : ∀ g, g < m → ∀ b,
      F (g * k + 1) (φ (g, b)).1 (φ (g, b)).2 ≠ F (g * k) (φ (g, b)).1 (φ (g, b)).2 := by
    intro g hg b
    have hle1 : g * k + 1 ≤ K := by
      have := hleK g hg; omega
    have hle0 : g * k ≤ K := (hi g hg).le
    cases b
    · simp only [φ]
      simp only [Bool.false_eq_true, ↓reduceIte]
      intro h
      rw [hanti _ hle1 _ _ (hrevE g hg), hanti _ hle0 _ _ (hrevE g hg)] at h
      exact (hvw g hg).2.2.1 (by linarith)
    · simp only [φ]; exact (hvw g hg).2.2.1
  have hconst : ∀ g, g < m → ∀ b, ∀ l, g * k + k ≤ l → l ≤ K →
      F l (φ (g, b)).1 (φ (g, b)).2 = F (g * k + k) (φ (g, b)).1 (φ (g, b)).2 := by
    intro g hg b l hl1 hl2
    cases b
    · simp only [φ]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hanti l hl2 _ _ (hrevE g hg), hanti (g * k + k) (hleK g hg) _ _ (hrevE g hg),
        hconst0 g hg l hl1 hl2]
    · simp only [φ]; exact hconst0 g hg l hl1 hl2
  have hdis : ∀ g g', g < g' → g' < m → ∀ b b', φ (g, b) ≠ φ (g', b') := by
    intro g g' hgg hg' b b' h
    have hs : g * k + k ≤ g' * k := by
      calc g * k + k = (g + 1) * k := by ring
        _ ≤ g' * k := Nat.mul_le_mul_right k hgg
    have hl2 : g' * k + 1 ≤ K := by
      have := hleK g' hg'; omega
    have hg : g < m := by omega
    have e1 := hconst g hg b (g' * k) hs (by omega)
    have e2 := hconst g hg b (g' * k + 1) (by omega) hl2
    have hc := hchg g' hg' b'
    rw [← h] at hc
    exact hc (e2.trans e1.symm)
  have hinj : Set.InjOn φ ↑(Finset.range m ×ˢ (Finset.univ : Finset Bool)) := by
    intro x hx y hy hxy
    obtain ⟨g, b⟩ := x
    obtain ⟨g', b'⟩ := y
    simp only [Finset.coe_product, Finset.coe_range, Finset.coe_univ, Set.mem_prod, Set.mem_Iio,
      Set.mem_univ, and_true] at hx hy
    rcases lt_trichotomy g g' with hlt | heq | hgt
    · exact absurd hxy (hdis g g' hlt hy b b')
    · subst heq
      cases b <;> cases b'
      · rfl
      · exfalso
        have := hxy
        simp only [φ] at this
        simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at this
        exact (hvw g hx).2.1 this.1.symm
      · exfalso
        have := hxy
        simp only [φ] at this
        simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at this
        exact (hvw g hx).2.1 this.1
      · rfl
    · exact absurd hxy.symm (hdis g' g hgt hx b' b)
  have hcard := Finset.card_le_card_of_injOn φ
    (fun x hx => by
      obtain ⟨g, b⟩ := x
      have hx' : g < m := by simpa using hx
      exact hφE g hx' b) hinj
  simp only [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool] at hcard
  omega

end CC579

open CycleCanceling.MinMean in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (hn : 2 ≤ Fintype.card V)
    (F : ℕ → V → V → ℝ) (K : ℕ) (hrun : IsMinMeanRun N F K) :
    K ≤ Fintype.card V * N.E.card ^ 2 * ⌈Real.log (Fintype.card V) + 1⌉₊ := by
  exact CC579.parent N hn F K hrun
