-- Prove2me | solution 1 for BunkbedFalse.sub_probability_grouping
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T09:18:33.375842+00:00
-- url     : https://prove2.me/submissions/cbc9cab1-d2fd-4ea0-ae33-93402c2c8b82

import Theorems.Thm_BunkbedAux_bbProb_biUnion_disjoint
import Theorems.Thm_BunkbedAux_reach_image_map
import Theorems.Thm_BunkbedAux_probOf_image_map
import Theorems.Thm_BunkbedFalse_bb_boundary_reduce

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph Function

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

namespace Grouping

def stateOf {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (a b c : V) : WZ :=
  if (ofEdges S).Reachable a b then
    (if (ofEdges S).Reachable b c then WZ.abc else WZ.ab_c)
  else if (ofEdges S).Reachable b c then WZ.a_bc
  else if (ofEdges S).Reachable a c then WZ.ac_b else WZ.a_b_c

theorem state_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (a b c : V) :
    ((ofEdges S).Reachable a b ↔ stateOf S a b c = .abc ∨ stateOf S a b c = .ab_c) ∧
    ((ofEdges S).Reachable b c ↔ stateOf S a b c = .abc ∨ stateOf S a b c = .a_bc) ∧
    ((ofEdges S).Reachable a c ↔ stateOf S a b c = .abc ∨ stateOf S a b c = .ac_b) := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      simp [stateOf, hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      simp [stateOf, hab, hbc, hac]
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hab (h.trans hbc.symm)
      simp [stateOf, hab, hbc, hac]
    · by_cases hac : (ofEdges S).Reachable a c
      · simp [stateOf, hab, hbc, hac]
      · simp [stateOf, hab, hbc, hac]

theorem state_event {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (a b c : V) (s : WZ) :
    stateOf S a b c = s ↔
      match s with
      | .abc => (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c
      | .ab_c => (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c
      | .ac_b => (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b
      | .a_bc => (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b
      | .a_b_c => ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
          ¬ (ofEdges S).Reachable a c := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      cases s <;> simp [stateOf, hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      cases s <;> simp [stateOf, hab, hbc, hac]
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hab (h.trans hbc.symm)
      cases s <;> simp [stateOf, hab, hbc, hac]
    · by_cases hac : (ofEdges S).Reachable a c
      · cases s <;> simp [stateOf, hab, hbc, hac]
      · cases s <;> simp [stateOf, hab, hbc, hac]

def partMass {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : WZ → ℚ
  | .abc => Pabc E w a b c
  | .ab_c => Pab_c E w a b c
  | .ac_b => Pac_b E w a b c
  | .a_bc => Pa_bc E w a b c
  | .a_b_c => Pa_b_c E w a b c

theorem prob_state_eq {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) (s : WZ) :
    probOf E w (fun S => stateOf S a b c = s) = partMass E w a b c s := by
  unfold probOf
  cases s <;> unfold partMass Pabc Pab_c Pac_b Pa_bc Pa_b_c probOf <;>
    apply Finset.sum_congr rfl <;> intro S hS <;>
    exact if_congr (state_event S a b c _ ) rfl rfl

theorem state_image {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) (a b c : V) :
    stateOf (S.image (Sym2.map f)) (f a) (f b) (f c) = stateOf S a b c := by
  unfold stateOf
  simp only [BunkbedAux.reach_image_map f hf]

theorem prob_state_image {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (a b d : V) (s : WZ) :
    probOf (E.image (Sym2.map f)) (fun _ => c)
        (fun S => stateOf S (f a) (f b) (f d) = s) =
      partMass E (fun _ => c) a b d s := by
  rw [← prob_state_eq E (fun _ => c) a b d s]
  exact (BunkbedAux.probOf_image_map f hf E c _ _
    (fun S _ => by rw [state_image f hf S a b d])).symm

lemma gadgetW_half (n : ℕ) : gadgetW n (1/2 : ℚ) = fun _ => (1/2 : ℚ) := by
  funext e
  unfold gadgetW
  split_ifs <;> norm_num

/-! The embedding is injective. The arithmetic proof follows the explicit block layout. -/

lemma tri_val (i : Fin 6) :
    (i.val = 0 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 0 ∧
        (hollomPath i.succ).val = 2) ∨
    (i.val = 1 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 2 ∧
        (hollomPath i.succ).val = 5) ∨
    (i.val = 2 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 5 ∧
        (hollomPath i.succ).val = 4) ∨
    (i.val = 3 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 4 ∧
        (hollomPath i.succ).val = 3) ∨
    (i.val = 4 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 3 ∧
        (hollomPath i.succ).val = 7) ∨
    (i.val = 5 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 7 ∧
        (hollomPath i.succ).val = 9) := by
  fin_cases i <;> simp [hollomTr, hollomPath]

lemma trv (i : Fin 6) : (hollomTr i).val = 1 ∨ (hollomTr i).val = 8 ∨
    (hollomTr i).val = 6 := by
  rcases tri_val i with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    omega

lemma pathv (j : Fin 7) : (hollomPath j).val = 0 ∨ (hollomPath j).val = 2 ∨
    (hollomPath j).val = 5 ∨ (hollomPath j).val = 4 ∨ (hollomPath j).val = 3 ∨
    (hollomPath j).val = 7 ∨ (hollomPath j).val = 9 := by
  fin_cases j <;> simp [hollomPath]

lemma tr_ne_path : ∀ (i : Fin 6) (j : Fin 7), hollomTr i ≠ hollomPath j := by
  intro i j h
  have hv : (hollomTr i).val = (hollomPath j).val := by rw [h]
  have h1 := trv i
  have h2 := pathv j
  omega

lemma cs_ne_succ : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by
  intro i h
  have hv : (hollomPath i.castSucc).val = (hollomPath i.succ).val := by rw [h]
  rcases tri_val i with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ |
    ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> omega

lemma embN_zero (i : Fin 6) : embN i 0 = (hollomTr i).val := by simp [embN]
lemma embN_one (i : Fin 6) : embN i 1 = (hollomPath i.castSucc).val := by simp [embN]
lemma embN_last (i : Fin 6) : embN i 1204 = (hollomPath i.succ).val := by simp [embN]

lemma embN_interior (i : Fin 6) (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≤ 1203) :
    embN i k = 10 + 1202 * i.val + (k - 2) := by
  unfold embN; split_ifs <;> omega

lemma embN_bdry (i : Fin 6) (k : ℕ) (h : k = 0 ∨ k = 1 ∨ k = 1204) : embN i k < 10 := by
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  rcases h with rfl | rfl | rfl <;> (unfold embN; split_ifs <;> omega)

lemma embN_bdry_inj (i : Fin 6) (k q : ℕ) (hk : k = 0 ∨ k = 1 ∨ k = 1204)
    (hq : q = 0 ∨ q = 1 ∨ q = 1204) (h : embN i k = embN i q) : k = q := by
  have n1 : (hollomTr i).val ≠ (hollomPath i.castSucc).val :=
    fun hh => tr_ne_path i i.castSucc (Fin.ext hh)
  have n2 : (hollomTr i).val ≠ (hollomPath i.succ).val :=
    fun hh => tr_ne_path i i.succ (Fin.ext hh)
  have n3 : (hollomPath i.castSucc).val ≠ (hollomPath i.succ).val :=
    fun hh => cs_ne_succ i (Fin.ext hh)
  rcases hk with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [embN_zero, embN_one, embN_last] at h <;> omega

lemma idx_cases (k : Fin 1205) :
    (k.val = 0 ∨ k.val = 1 ∨ k.val = 1204) ∨ (2 ≤ k.val ∧ k.val ≤ 1203) := by
  have := k.isLt; omega

lemma emb_inj (i : Fin 6) : Injective (emb i) := by
  intro k q h
  have hv : embN i k.val = embN i q.val := congrArg Fin.val h
  rcases idx_cases k with hk | hk <;> rcases idx_cases q with hq | hq
  · exact Fin.ext (embN_bdry_inj i k.val q.val hk hq hv)
  · have h1 := embN_bdry i k.val hk
    have h2 := embN_interior i q.val hq.1 hq.2
    omega
  · have h1 := embN_bdry i q.val hq
    have h2 := embN_interior i k.val hk.1 hk.2
    omega
  · have h1 := embN_interior i k.val hk.1 hk.2
    have h2 := embN_interior i q.val hq.1 hq.2
    exact Fin.ext (by omega)

theorem copy_state_mass
    (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (i : Fin 6) (s : WZ) :
    probOf ((gadgetE 1204).image (Sym2.map (emb i))) (fun _ => (1/2 : ℚ))
        (fun S => stateOf S (emb i 0) (emb i 1) (emb i 1204) = s) = P s := by
  change probOf ((gadgetE 1204).image (Sym2.map (emb i))) (fun _ => (1/2 : ℚ))
      (fun S => stateOf S (emb i 0) (emb i 1) (emb i (Fin.last 1204)) = s) = P s
  rw [prob_state_image (emb i) (emb_inj i) (gadgetE 1204) (1/2) 0 1 (Fin.last 1204) s]
  rw [← gadgetW_half 1204]
  cases s <;> simp only [partMass] <;> symm <;> assumption

theorem pi_pushforward_sum
    {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    {A : I → Type*}
    (D : ∀ i, Finset (A i)) (st : ∀ i, A i → B) (mu : ∀ i, A i → ℚ)
    (P : I → B → ℚ)
    (hmass : ∀ i b, ∑ a ∈ D i with st i a = b, mu i a = P i b)
    (F : (I → B) → ℚ) :
    (∑ a ∈ Fintype.piFinset D, F (fun i => st i (a i)) * ∏ i, mu i (a i)) =
      ∑ b : I → B, F b * ∏ i, P i (b i) := by
  classical
  let q : (∀ i, A i) → (I → B) := fun a i => st i (a i)
  calc
    _ = ∑ b : I → B, ∑ a ∈ Fintype.piFinset D with q a = b,
          F (q a) * ∏ i, mu i (a i) := by
      rw [Finset.sum_fiberwise (Fintype.piFinset D) q
        (fun a => F (q a) * ∏ i, mu i (a i))]
    _ = ∑ b : I → B, F b * ∏ i, P i (b i) := by
      apply Finset.sum_congr rfl
      intro b _
      have hpi :
          (Fintype.piFinset (fun i => (D i).filter (fun a => st i a = b i))) =
            (Fintype.piFinset D).filter (fun a => q a = b) := by
        ext a
        simp only [Fintype.mem_piFinset, mem_filter, q]
        constructor
        · intro h
          exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩
        · rintro ⟨hD, hq⟩ i
          exact ⟨hD i, congrFun hq i⟩
      rw [← hpi]
      have hF : ∀ a ∈ Fintype.piFinset (fun i => (D i).filter (fun x => st i x = b i)),
          F (q a) = F b := by
        intro a ha
        congr 1
        funext i
        exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp ha i)).2
      rw [Finset.sum_congr rfl (fun a ha => by rw [hF a ha]), ← Finset.mul_sum]
      rw [← Finset.prod_univ_sum]
      simp_rw [hmass]

theorem one_level_push
    (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (F : (Fin 6 → WZ) → ℚ) :
    (∑ S ∈ Fintype.piFinset (fun i : Fin 6 =>
          ((gadgetE 1204).image (Sym2.map (emb i))).powerset),
        F (fun i => stateOf (S i) (emb i 0) (emb i 1) (emb i 1204)) *
          ∏ i, weight ((gadgetE 1204).image (Sym2.map (emb i)))
            (fun _ => (1/2 : ℚ)) (S i)) =
      ∑ φ : Fin 6 → WZ, F φ * ∏ i, P (φ i) := by
  let E : Fin 6 → Finset (Sym2 (Fin 7222)) :=
    fun i => (gadgetE 1204).image (Sym2.map (emb i))
  let st : (i : Fin 6) → Finset (Sym2 (Fin 7222)) → WZ :=
    fun i S => stateOf S (emb i 0) (emb i 1) (emb i 1204)
  let mu : (i : Fin 6) → Finset (Sym2 (Fin 7222)) → ℚ :=
    fun i S => weight (E i) (fun _ => (1/2 : ℚ)) S
  have hm : ∀ i s, ∑ S ∈ (E i).powerset with st i S = s, mu i S = P s := by
    intro i s
    rw [← copy_state_mass P habc hab hac hbc hsep i s]
    unfold probOf
    rw [Finset.sum_filter]
  exact pi_pushforward_sum (fun i => (E i).powerset) st mu (fun _ => P) hm F

def twoLevel {I A : Type*} (q : (I → A) × (I → A)) (p : I × Fin 2) : A :=
  if p.2 = 0 then q.1 p.1 else q.2 p.1

def twoLevelEquiv {I A : Type*} : ((I → A) × (I → A)) ≃ (I × Fin 2 → A) where
  toFun := twoLevel
  invFun f := (fun i => f (i, 0), fun i => f (i, 1))
  left_inv q := by
    ext i <;> simp [twoLevel]
  right_inv f := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp [twoLevel]

theorem twoLevel_prod (P : WZ → ℚ) (φ₀ φ₁ : Fin 6 → WZ) :
    (∏ p : Fin 6 × Fin 2, P (twoLevel (φ₀, φ₁) p)) =
      (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i) := by
  rw [Fintype.prod_prod_type]
  simp_rw [Fin.prod_univ_two]
  simp only [twoLevel, if_pos, Fin.isValue, OfNat.ofNat, if_false]
  exact Finset.prod_mul_distrib

def copyStates (S : Fin 6 → Finset (Sym2 (Fin 7222))) : Fin 6 → WZ :=
  fun i => stateOf (S i) (emb i 0) (emb i 1) (emb i 1204)

theorem selected_state_match
    (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) :
    ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1) ↔
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .abc ∨
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .ab_c) ∧
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 1) (emb i 1204) ↔
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .abc ∨
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .a_bc) ∧
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1204) ↔
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .abc ∨
          twoLevel (copyStates S₀, copyStates S₁) (i, l) = .ac_b) := by
  intro i l
  by_cases hl : l = 0
  · subst l
    simpa only [twoLevel, copyStates, if_pos] using
      state_boundary (S₀ i) (emb i 0) (emb i 1) (emb i 1204)
  · have hl1 : l = 1 := Fin.eq_one_of_ne_zero l hl
    subst l
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simpa only [twoLevel, copyStates, h10, if_false] using
      state_boundary (S₁ i) (emb i 0) (emb i 1) (emb i 1204)


end Grouping


namespace Grouping

theorem configuration_subset {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → Finset A) (S : I → Finset A)
    (hS : S ∈ Fintype.piFinset (fun i => (E i).powerset)) :
    ∀ i, S i ⊆ E i := by
  intro i
  exact Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)

theorem push_two {A B : Type*} [Fintype B]
    (D : Finset A) (st : A → B) (mu : A → ℚ) (P : B → ℚ)
    (hpush : ∀ F : B → ℚ, (∑ a ∈ D, F (st a) * mu a) = ∑ b, F b * P b)
    (F : B → B → ℚ) :
    (∑ a₀ ∈ D, ∑ a₁ ∈ D, F (st a₀) (st a₁) * mu a₀ * mu a₁) =
      ∑ b₀, ∑ b₁, F b₀ b₁ * P b₀ * P b₁ := by
  classical
  calc
    _ = ∑ a₀ ∈ D, ∑ b₁, (F (st a₀) b₁ * mu a₀) * P b₁ := by
      exact Finset.sum_congr rfl (fun a₀ _ => hpush (fun b₁ => F (st a₀) b₁ * mu a₀))
    _ = ∑ b₁, ∑ a₀ ∈ D, (F (st a₀) b₁ * P b₁) * mu a₀ := by
      rw [Finset.sum_comm]
      congr 1
      funext b₁
      exact Finset.sum_congr rfl (fun a₀ _ => mul_right_comm _ _ _)
    _ = ∑ b₁, ∑ b₀, (F b₀ b₁ * P b₁) * P b₀ := by
      exact Finset.sum_congr rfl (fun b₁ _ => hpush (fun b₀ => F b₀ b₁ * P b₁))
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b₀ _ =>
        Finset.sum_congr rfl (fun b₁ _ => mul_right_comm _ _ _))

theorem pair_state_sum (P : WZ → ℚ) (C : (Fin 6 × Fin 2 → WZ) → ℚ) :
    (∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
      C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i)) =
      ∑ ψ : Fin 6 × Fin 2 → WZ, C ψ * ∏ p, P (ψ p) := by
  rw [← Fintype.sum_prod_type' (fun φ₀ φ₁ : Fin 6 → WZ =>
    C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i))]
  refine Fintype.sum_equiv twoLevelEquiv _ _ ?_
  rintro ⟨φ₀, φ₁⟩
  change C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * (∏ i, P (φ₁ i)) =
    C (twoLevel (φ₀, φ₁)) * ∏ p, P (twoLevel (φ₀, φ₁) p)
  rw [twoLevel_prod, mul_assoc]

theorem sum_indicator_congr {A : Type*} (D : Finset A) (mu : A → ℚ)
    (ev ev' : A → A → Prop) [DecidableRel ev] [DecidableRel ev']
    (h : ∀ a ∈ D, ∀ b ∈ D, ev a b ↔ ev' a b) :
    (∑ a ∈ D, ∑ b ∈ D, (if ev a b then 1 else 0) * mu a * mu b) =
      ∑ a ∈ D, ∑ b ∈ D, (if ev' a b then 1 else 0) * mu a * mu b := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun z : ℚ => z * mu a * mu b)
    (if_congr (h a ha b hb) rfl rfl)

end Grouping

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph Function
set_option maxRecDepth 2000
-- Keep concrete configuration spaces opaque during elaboration.
attribute [local irreducible] Fintype.piFinset gadgetE
set_option maxHeartbeats 200000
namespace Grouping
theorem configuration_reach
    (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hS₀ : S₀ ∈ Fintype.piFinset (fun i : Fin 6 =>
      ((gadgetE 1204).image (Sym2.map (emb i))).powerset))
    (hS₁ : S₁ ∈ Fintype.piFinset (fun i : Fin 6 =>
      ((gadgetE 1204).image (Sym2.map (emb i))).powerset))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (iota x, 0) (iota y, l) ↔
      (wzGraph hollomTriple hollomT
        (twoLevel (copyStates S₀, copyStates S₁))).Reachable
        (x, 0) (y, l) := by
  exact BunkbedFalse.bb_boundary_reduce S₀ S₁
    (configuration_subset (I := Fin 6) (A := Sym2 (Fin 7222)) (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i))) S₀ hS₀)
    (configuration_subset (I := Fin 6) (A := Sym2 (Fin 7222)) (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i))) S₁ hS₁)
    (twoLevel (copyStates S₀, copyStates S₁)) (selected_state_match S₀ S₁) x y l
end Grouping

open Grouping

theorem solution
    (hdisj : ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))))
    (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by
  let E : Fin 6 → Finset (Sym2 (Fin 7222)) :=
    fun i => (gadgetE 1204).image (Sym2.map (emb i))
  let D := Fintype.piFinset (fun i : Fin 6 => (E i).powerset)
  let mu : (Fin 6 → Finset (Sym2 (Fin 7222))) → ℚ :=
    fun S => ∏ i, weight (E i) (fun _ => (1/2 : ℚ)) (S i)
  let C : (Fin 6 × Fin 2 → WZ) → ℚ := fun ψ =>
    if (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) then 1 else 0
  have hpush : ∀ F : (Fin 6 → WZ) → ℚ,
      (∑ S ∈ D, F (copyStates S) * mu S) =
        ∑ φ : Fin 6 → WZ, F φ * ∏ i, P (φ i) := by
    intro F
    exact one_level_push P habc hab hac hbc hsep F
  calc
    _ = ∑ S₀ ∈ D, ∑ S₁ ∈ D,
        (if (bbGraph subT (Finset.univ.biUnion S₀)
          (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l) then 1 else 0) *
          mu S₀ * mu S₁ :=
      BunkbedAux.bbProb_biUnion_disjoint E hdisj (fun _ => (1/2 : ℚ)) subT
        (iota x, 0) (iota y, l)
    _ = ∑ S₀ ∈ D, ∑ S₁ ∈ D,
        C (twoLevel (copyStates S₀, copyStates S₁)) * mu S₀ * mu S₁ := by
      exact sum_indicator_congr D mu
        (fun S₀ S₁ => (bbGraph subT (Finset.univ.biUnion S₀)
          (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l))
        (fun S₀ S₁ => (wzGraph hollomTriple hollomT
          (twoLevel (copyStates S₀, copyStates S₁))).Reachable (x, 0) (y, l))
        (fun S₀ hS₀ S₁ hS₁ => configuration_reach S₀ S₁ hS₀ hS₁ x y l)
    _ = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
        C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i) :=
      push_two D copyStates mu (fun φ => ∏ i, P (φ i)) hpush
        (fun φ₀ φ₁ => C (twoLevel (φ₀, φ₁)))
    _ = _ := pair_state_sum P C




