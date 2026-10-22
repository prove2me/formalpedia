-- Prove2me | solution 1 for ConstrNestedLogit.Reduce.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:35:43.369774+00:00
-- url     : https://prove2.me/submissions/61c5a725-d9c7-4f4e-a0d5-f10373456615

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Reduce_Problems

set_option autoImplicit false

/-- Per-nest bound behind Lemma 3 (Gallego-Topaloglu): with the threshold
`u = max(Z, γ Z + (1-γ) R*)`, an `α`-approximate maximiser of `V (R - u)` (which also beats the
empty assortment) satisfies `V̂^γ (α R̂ - Z) ≥ V*^γ (R* - Z)`. -/
lemma cnl4_nest_bound (Vs Rs Vh Rh Z γ α : ℝ) (hVs : 0 ≤ Vs) (hVh : 0 ≤ Vh) (hZ : 0 ≤ Z)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα : 1 ≤ α)
    (h1 : Vs * (Rs - max Z (γ * Z + (1 - γ) * Rs))
      ≤ α * (Vh * (Rh - max Z (γ * Z + (1 - γ) * Rs))))
    (h2 : 0 ≤ α * (Vh * (Rh - max Z (γ * Z + (1 - γ) * Rs)))) :
    Vs ^ γ * (Rs - Z) ≤ Vh ^ γ * (α * Rh - Z) := by
  set u := max Z (γ * Z + (1 - γ) * Rs) with hudef
  have hZu : Z ≤ u := le_max_left _ _
  have hα0 : 0 < α := by linarith
  have hL : 0 ≤ Vh ^ γ * (α * Rh - Z) := by
    rcases hVh.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hγ0.ne', zero_mul]
    · apply mul_nonneg (Real.rpow_nonneg hVh _)
      have hRu : 0 ≤ Rh - u := by
        by_contra hc
        rw [not_le] at hc
        have : α * (Vh * (Rh - u)) < 0 := mul_neg_of_pos_of_neg hα0 (mul_neg_of_pos_of_neg h hc)
        linarith
      nlinarith
  rcases le_or_gt Rs Z with hRs | hRs
  · calc Vs ^ γ * (Rs - Z) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hVs _) (by linarith)
      _ ≤ _ := hL
  rcases hVs.eq_or_lt with hV0 | hV0
  · rw [← hV0, Real.zero_rpow hγ0.ne', zero_mul]
    exact hL
  have hu' : u = γ * Z + (1 - γ) * Rs := max_eq_right (by nlinarith)
  have hD : 0 < Rs - Z := by linarith
  have e1 : Vs * (Rs - u) = γ * Vs * (Rs - Z) := by rw [hu']; ring
  have h1' : γ * Vs * (Rs - Z) ≤ α * (Vh * (Rh - u)) := by linarith
  have hpos : 0 < γ * Vs * (Rs - Z) := mul_pos (mul_pos hγ0 hV0) hD
  have hVh0 : 0 < Vh := by
    rcases hVh.eq_or_lt with h | h
    · rw [← h] at h1'
      simp at h1'
      linarith
    · exact h
  have bern : (Vs / Vh) ^ γ ≤ γ * (Vs / Vh) + (1 - γ) := by
    have := Real.geom_mean_le_arith_mean2_weighted hγ0.le (by linarith : (0:ℝ) ≤ 1 - γ)
      (div_nonneg hVs hVh) zero_le_one (by ring)
    simpa [Real.one_rpow] using this
  have hq : γ * (Vs / Vh) * (Rs - Z) ≤ α * (Rh - u) := by
    have e2 : γ * (Vs / Vh) * (Rs - Z) = (γ * Vs * (Rs - Z)) / Vh := by
      field_simp
    rw [e2, div_le_iff₀ hVh0]
    have e3 : α * (Vh * (Rh - u)) = α * (Rh - u) * Vh := by ring
    linarith
  have huZ : u - Z = (1 - γ) * (Rs - Z) := by rw [hu']; ring
  have hu0 : 0 ≤ u := le_trans hZ hZu
  have hαu : u - Z ≤ α * u - Z := by nlinarith
  have key : (Rs - Z) * (Vs / Vh) ^ γ ≤ α * Rh - Z := by
    calc (Rs - Z) * (Vs / Vh) ^ γ ≤ (Rs - Z) * (γ * (Vs / Vh) + (1 - γ)) :=
          mul_le_mul_of_nonneg_left bern hD.le
      _ = γ * (Vs / Vh) * (Rs - Z) + (1 - γ) * (Rs - Z) := by ring
      _ ≤ α * (Rh - u) + (u - Z) := by linarith
      _ ≤ α * Rh - Z := by nlinarith
  have hWpos : 0 < Vh ^ γ := Real.rpow_pos_of_pos hVh0 γ
  calc Vs ^ γ * (Rs - Z) = Vh ^ γ * ((Rs - Z) * (Vs / Vh) ^ γ) := by
        rw [Real.div_rpow hVs hVh0.le]
        field_simp
    _ ≤ Vh ^ γ * (α * Rh - Z) := mul_le_mul_of_nonneg_left key hWpos.le

open NestedLogitVariants.LP ConstrNestedLogit.Reduce in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n) (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (C : ι → Set (Finset (Fin n))) (h0 : ∀ i, ∅ ∈ C i)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal1 I C Sstar)
    (α : ℝ) (hα : 1 ≤ α)
    (A : ι → Set (Finset (Fin n))) (hAC : ∀ i, A i ⊆ C i)
    (hA : ∀ i, ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A i, IsApproxSol7 I C i α u S) :
    ∃ Shat : ι → Finset (Fin n),
      (∀ i, Shat i ∈ A i) ∧ revenue I Sstar ≤ α * revenue I Shat := by
  have hV0 : ∀ i, V I i ∅ = 0 := fun i => by simp [V, hvnp]
  have hW0 : ∀ i, nestWeight I i ∅ = 0 := fun i => by
    simp [nestWeight, hV0, Real.zero_rpow (hγ i).1.ne']
  have hVnn : ∀ i S, 0 ≤ V I i S := fun i S => by
    simp only [V, hvnp, zero_add]
    exact Finset.sum_nonneg (fun j _ => (hv i j).le)
  have hZ : 0 ≤ revenue I Sstar := by
    have h := hopt.2 (fun _ => ∅) (fun i => h0 i)
    have e : revenue I (fun _ => ∅) = 0 := by simp [revenue, hW0]
    linarith
  have hu : ∀ i, 0 ≤ uStar I Sstar i := fun i => le_trans hZ (le_max_left _ _)
  choose Shat hShatA hShat using fun i => hA i (uStar I Sstar i) (hu i)
  refine ⟨Shat, hShatA, ?_⟩
  have hnest : ∀ i, nestWeight I i (Sstar i) * (R I i (Sstar i) - revenue I Sstar)
      ≤ nestWeight I i (Shat i) * (α * R I i (Shat i) - revenue I Sstar) := by
    intro i
    have h1 := (hShat i).2 (Sstar i) (hopt.1 i)
    have h2 := (hShat i).2 ∅ (h0 i)
    simp only [obj7, uStar] at h1 h2
    rw [hV0, zero_mul] at h2
    exact cnl4_nest_bound _ _ _ _ _ _ _ (hVnn _ _) (hVnn _ _) hZ (hγ i).1 (hγ i).2 hα h1 h2
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hnest i)
  have hWnn : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hVnn i S) _
  have hden : 0 < I.v0 + ∑ i, nestWeight I i (Sstar i) :=
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg (fun i _ => hWnn i _))
  have hdenh : 0 < I.v0 + ∑ i, nestWeight I i (Shat i) :=
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg (fun i _ => hWnn i _))
  have hZmul : revenue I Sstar * (I.v0 + ∑ i, nestWeight I i (Sstar i))
      = ∑ i, nestWeight I i (Sstar i) * R I i (Sstar i) := by
    unfold revenue
    exact div_mul_cancel₀ _ hden.ne'
  have eL : ∑ i, nestWeight I i (Sstar i) * (R I i (Sstar i) - revenue I Sstar)
      = ∑ i, nestWeight I i (Sstar i) * R I i (Sstar i)
        - revenue I Sstar * ∑ i, nestWeight I i (Sstar i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have eR : ∑ i, nestWeight I i (Shat i) * (α * R I i (Shat i) - revenue I Sstar)
      = α * ∑ i, nestWeight I i (Shat i) * R I i (Shat i)
        - revenue I Sstar * ∑ i, nestWeight I i (Shat i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [eL, eR] at hsum
  have goal' : revenue I Sstar * (I.v0 + ∑ i, nestWeight I i (Shat i))
      ≤ α * ∑ i, nestWeight I i (Shat i) * R I i (Shat i) := by
    nlinarith
  show revenue I Sstar ≤ α * ((∑ i, nestWeight I i (Shat i) * R I i (Shat i))
      / (I.v0 + ∑ i, nestWeight I i (Shat i)))
  rw [mul_div_assoc', le_div_iff₀ hdenh]
  exact goal'
