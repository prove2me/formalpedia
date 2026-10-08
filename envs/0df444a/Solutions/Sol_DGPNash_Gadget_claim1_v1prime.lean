-- Prove2me | solution 1 for DGPNash.Gadget.claim1_v1prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:04:42.846645+00:00
-- url     : https://prove2.me/submissions/ee762e83-7f60-4c67-8d5d-d59f09a621c0

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace P67f5231d

open DGPNash.Gadget

lemma exp_prod (τ : ∀ r, AddMulStrat r → ℝ) (h : ∀ r, AddMulStrat r → ℝ) :
    ∑ s : (∀ r, AddMulStrat r), AGT.profileProb τ s * ∏ i, h i (s i)
      = ∏ i, ∑ a, τ i a * h i a := by
  unfold AGT.profileProb
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => τ i a * h i a)).symm

lemma univ_eq : (Finset.univ : Finset AddMulRole) =
    {.v1, .v2, .v3, .w1, .v1', .w2, .v2', .w3, .w, .u} := by
  ext x; cases x <;> simp

lemma prod10 (f : AddMulRole → ℝ) : ∏ i, f i =
    f .v1 * (f .v2 * (f .v3 * (f .w1 * (f .v1' * (f .w2 * (f .v2' * (f .w3 * (f .w * f .u)))))))) := by
  rw [univ_eq]
  simp [Finset.prod_insert]

/-- w1 plays 0 term. -/
noncomputable def H1 : ∀ r, AddMulStrat r → ℝ := fun r => match r with
  | .w1 => fun (a : Fin 2) => if a = 0 then 1 / 8 else 0
  | .v1 => fun (a : Fin 2) => if a = 1 then 1 else 0
  | _ => fun _ => 1

/-- w1 plays 1 term. -/
noncomputable def H2 : ∀ r, AddMulStrat r → ℝ := fun r => match r with
  | .w1 => fun (a : Fin 2) => if a = 1 then 1 else 0
  | .v1' => fun (a : Fin 2) => if a = 1 then 1 else 0
  | _ => fun _ => 1

/-- v1' plays 0 term. -/
noncomputable def G1 : ∀ r, AddMulStrat r → ℝ := fun r => match r with
  | .v1' => fun (a : Fin 2) => if a = 0 then 1 else 0
  | .w1 => fun (a : Fin 2) => if a = 1 then 1 else 0
  | _ => fun _ => 1

/-- v1' plays 1 term. -/
noncomputable def G2 : ∀ r, AddMulStrat r → ℝ := fun r => match r with
  | .v1' => fun (a : Fin 2) => if a = 1 then 1 else 0
  | .w1 => fun (a : Fin 2) => if a = 0 then 1 else 0
  | _ => fun _ => 1

lemma fin2 (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨_ | _ | n, h⟩
  · left; rfl
  · right; rfl
  · omega

noncomputable def F1 (a b c : Fin 2) : ℝ := if a = 0 then (1 / 8 : ℝ) * ind (b = 1) else ind (c = 1)

noncomputable def F2 (a c : Fin 2) : ℝ := if c = 0 then ind (a = 1) else ind (a = 0)

lemma u_w1 (α β γ : ℕ) (s : ∀ r, AddMulStrat r) :
    addMulPayoff α β γ .w1 s = ∏ i, H1 i (s i) + ∏ i, H2 i (s i) := by
  have e : addMulPayoff α β γ .w1 s = F1 (s .w1) (s .v1) (s .v1') := rfl
  rw [e, prod10, prod10]
  dsimp only [H1, H2]
  generalize s .w1 = a
  generalize s .v1 = b
  generalize s .v1' = c
  rcases fin2 a with rfl | rfl <;> rcases fin2 b with rfl | rfl <;>
    rcases fin2 c with rfl | rfl <;> norm_num [F1, ind]

lemma u_v1' (α β γ : ℕ) (s : ∀ r, AddMulStrat r) :
    addMulPayoff α β γ .v1' s = ∏ i, G1 i (s i) + ∏ i, G2 i (s i) := by
  have e : addMulPayoff α β γ .v1' s = F2 (s .w1) (s .v1') := rfl
  rw [e, prod10, prod10]
  dsimp only [G1, G2]
  generalize s .w1 = a
  generalize s .v1' = c
  rcases fin2 a with rfl | rfl <;> rcases fin2 c with rfl | rfl <;> norm_num [F2, ind]

lemma pay_split (α β γ : ℕ) (τ : ∀ r, AddMulStrat r → ℝ) (r : AddMulRole)
    (A B : ∀ r, AddMulStrat r → ℝ)
    (hu : ∀ s, addMulPayoff α β γ r s = ∏ i, A i (s i) + ∏ i, B i (s i)) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ r =
      ∏ i, ∑ a, τ i a * A i a + ∏ i, ∑ a, τ i a * B i a := by
  unfold AGT.expectedPayoff
  simp_rw [hu, mul_add, Finset.sum_add_distrib, exp_prod]

lemma sum_v1 (f : AddMulStrat .v1 → ℝ) : ∑ a, f a = f (0 : Fin 2) + f (1 : Fin 2) :=
  Fin.sum_univ_two f

lemma sum_w1 (f : AddMulStrat .w1 → ℝ) : ∑ a, f a = f (0 : Fin 2) + f (1 : Fin 2) :=
  Fin.sum_univ_two f

lemma sum_v1p (f : AddMulStrat .v1' → ℝ) : ∑ a, f a = f (0 : Fin 2) + f (1 : Fin 2) :=
  Fin.sum_univ_two f

lemma ne10_w1 : ¬ @Eq (AddMulStrat .w1) (1 : Fin 2) (0 : Fin 2) :=
  fun h => absurd (congrArg Fin.val h) (by decide)
lemma ne01_w1 : ¬ @Eq (AddMulStrat .w1) (0 : Fin 2) (1 : Fin 2) :=
  fun h => absurd (congrArg Fin.val h) (by decide)
lemma ne10_v1p : ¬ @Eq (AddMulStrat .v1') (1 : Fin 2) (0 : Fin 2) :=
  fun h => absurd (congrArg Fin.val h) (by decide)
lemma ne01_v1p : ¬ @Eq (AddMulStrat .v1') (0 : Fin 2) (1 : Fin 2) :=
  fun h => absurd (congrArg Fin.val h) (by decide)

lemma pay_w1_0 (α β γ : ℕ) (σ : ∀ r, AddMulStrat r → ℝ) (hs : ∀ i, ∑ a, σ i a = 1) :
    DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w1 (0 : Fin 2) = 1 / 8 * σ .v1 (1 : Fin 2) := by
  unfold DGPNash.NashMap.purePayoff
  rw [pay_split α β γ _ .w1 H1 H2 (u_w1 α β γ), prod10, prod10]
  dsimp only [H1, H2]
  simp [Function.update_of_ne, hs, sum_v1, sum_w1, sum_v1p, ne10_w1, ne01_w1, ne10_v1p, ne01_v1p]
  all_goals first
    | ring1
    | (split_ifs with h <;> first | ring1 | exact absurd rfl h)
    | (intro h; exact absurd rfl h)

lemma pay_w1_1 (α β γ : ℕ) (σ : ∀ r, AddMulStrat r → ℝ) (hs : ∀ i, ∑ a, σ i a = 1) :
    DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w1 (1 : Fin 2) = σ .v1' (1 : Fin 2) := by
  unfold DGPNash.NashMap.purePayoff
  rw [pay_split α β γ _ .w1 H1 H2 (u_w1 α β γ), prod10, prod10]
  dsimp only [H1, H2]
  simp [Function.update_of_ne, hs, sum_v1, sum_w1, sum_v1p, ne10_w1, ne01_w1, ne10_v1p, ne01_v1p]
  all_goals first
    | ring1
    | (split_ifs with h <;> first | ring1 | exact absurd rfl h)
    | (intro h; exact absurd rfl h)

lemma pay_v1p_0 (α β γ : ℕ) (σ : ∀ r, AddMulStrat r → ℝ) (hs : ∀ i, ∑ a, σ i a = 1) :
    DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v1' (0 : Fin 2) = σ .w1 (1 : Fin 2) := by
  unfold DGPNash.NashMap.purePayoff
  rw [pay_split α β γ _ .v1' G1 G2 (u_v1' α β γ), prod10, prod10]
  dsimp only [G1, G2]
  simp [Function.update_of_ne, hs, sum_v1, sum_w1, sum_v1p, ne10_w1, ne01_w1, ne10_v1p, ne01_v1p]
  all_goals first
    | ring1
    | (split_ifs with h <;> first | ring1 | exact absurd rfl h)
    | (intro h; exact absurd rfl h)

lemma pay_v1p_1 (α β γ : ℕ) (σ : ∀ r, AddMulStrat r → ℝ) (hs : ∀ i, ∑ a, σ i a = 1) :
    DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v1' (1 : Fin 2) = σ .w1 (0 : Fin 2) := by
  unfold DGPNash.NashMap.purePayoff
  rw [pay_split α β γ _ .v1' G1 G2 (u_v1' α β γ), prod10, prod10]
  dsimp only [G1, G2]
  simp [Function.update_of_ne, hs, sum_v1, sum_w1, sum_v1p, ne10_w1, ne01_w1, ne10_v1p, ne01_v1p]
  all_goals first
    | ring1
    | (split_ifs with h <;> first | ring1 | exact absurd rfl h)
    | (intro h; exact absurd rfl h)

theorem main (α β γ : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v1' (1 : Fin 2) - (1 / 8) * σ .v1 (1 : Fin 2)| ≤ ε := by
  obtain ⟨hmix, hws⟩ := hσ
  have hs : ∀ i, ∑ a, σ i a = 1 := fun i => (hmix i).2
  have sw1 : σ .w1 (0 : Fin 2) + σ .w1 (1 : Fin 2) = 1 := by
    rw [← hs .w1]; exact (Fin.sum_univ_two _).symm
  have sv1 : σ .v1 (0 : Fin 2) + σ .v1 (1 : Fin 2) = 1 := by
    rw [← hs .v1]; exact (Fin.sum_univ_two _).symm
  have sv1' : σ .v1' (0 : Fin 2) + σ .v1' (1 : Fin 2) = 1 := by
    rw [← hs .v1']; exact (Fin.sum_univ_two _).symm
  have n1 : 0 ≤ σ .v1 (0 : Fin 2) := (hmix .v1).1 _
  have n2 : 0 ≤ σ .v1 (1 : Fin 2) := (hmix .v1).1 _
  have n3 : 0 ≤ σ .w1 (0 : Fin 2) := (hmix .w1).1 _
  have n4 : 0 ≤ σ .w1 (1 : Fin 2) := (hmix .w1).1 _
  have Hw01 := hws .w1 (0 : Fin 2) (1 : Fin 2)
  have Hw10 := hws .w1 (1 : Fin 2) (0 : Fin 2)
  have Hv01 := hws .v1' (0 : Fin 2) (1 : Fin 2)
  have Hv10 := hws .v1' (1 : Fin 2) (0 : Fin 2)
  rw [pay_w1_0 α β γ σ hs, pay_w1_1 α β γ σ hs] at Hw01 Hw10
  rw [pay_v1p_0 α β γ σ hs, pay_v1p_1 α β γ σ hs] at Hv01 Hv10
  rw [abs_le]
  constructor
  · by_contra h
    rw [not_le] at h
    have h1 : σ .w1 (1 : Fin 2) = 0 := Hw01 (by linarith)
    have h2 : σ .v1' (0 : Fin 2) = 0 := Hv10 (by rw [h1]; linarith)
    linarith
  · by_contra h
    rw [not_le] at h
    have h1 : σ .w1 (0 : Fin 2) = 0 := Hw10 (by linarith)
    have h2 : σ .v1' (1 : Fin 2) = 0 := Hv01 (by rw [h1]; linarith)
    linarith

end P67f5231d

open DGPNash.Gadget in
theorem solution (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v1' (1 : Fin 2) - (1 / 8) * σ .v1 (1 : Fin 2)| ≤ ε := by
  exact P67f5231d.main α β γ ε hε0 hε σ hσ
