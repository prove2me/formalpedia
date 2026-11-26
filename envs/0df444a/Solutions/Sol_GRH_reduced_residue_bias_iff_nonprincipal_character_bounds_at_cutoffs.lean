-- Prove2me | solution 1 for GRH.reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:05:09.696387+00:00
-- url     : https://prove2.me/submissions/6790b924-3caf-4061-af28-d5c2ed812745

import Theorems.Thm_FamousTheorems_dirichlet_character_orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

noncomputable section

local instance {q : ℕ} [NeZero q] : Fintype (DirichletCharacter ℂ q) :=
  @Fintype.ofFinite _ (Finite.of_equiv ((ZMod q)ˣ →* ℂˣ) MulChar.equivToUnitHom.symm)

private theorem kernel (q : ℕ) [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b) =
      if a = b then (q.totient : ℂ) else 0 := by
  classical
  have off (t : ZMod q) (ht : t ≠ 1) :
      (∑ χ : DirichletCharacter ℂ q, χ t) = 0 :=
    FamousTheorems.dirichlet_character_orthogonality ℂ ht
  have byResidue : (∑ t : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ t) =
      ∑ χ : DirichletCharacter ℂ q, χ (1 : ZMod q) := by
    apply Finset.sum_eq_single 1
    · exact fun t _ ht => off t ht
    · simp
  have byCharacter : (∑ χ : DirichletCharacter ℂ q, ∑ t : ZMod q, χ t) =
      (q.totient : ℂ) := by
    calc
      _ = ∑ t : ZMod q, (1 : DirichletCharacter ℂ q) t := by
        apply Finset.sum_eq_single 1
        · exact fun χ _ hχ => χ.sum_eq_zero_of_ne_one hχ
        · simp
      _ = _ := by rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  have diag : (∑ χ : DirichletCharacter ℂ q, χ (1 : ZMod q)) = (q.totient : ℂ) := by
    rw [← byResidue, Finset.sum_comm]
    exact byCharacter
  simp only [← map_mul]
  by_cases h : a = b
  · rw [if_pos h, (ZMod.inv_mul_eq_one_of_isUnit ha b).mpr h]
    exact diag
  · rw [if_neg h]
    exact off _ (fun hz => h ((ZMod.inv_mul_eq_one_of_isUnit ha b).mp hz))

private theorem bounded_finite_sum {ι : Type} [Fintype ι] (f : ι → ℕ → ℂ) (g : ℕ → ℝ)
    (h : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖f i u‖ ≤ C * g u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖∑ i, f i u‖ ≤ C * g u := by
  choose c hc hu using h
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), fun u => ?_⟩
  rw [Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hu i u)

theorem solution (q : ℕ) [NeZero q] (w : ℕ → ℝ) (n : ℕ → ℕ) (g : ℕ → ℝ) :
    (∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (n u + 1), if (k : ZMod q) = a then w k else 0) -
        (∑ k ∈ Finset.range (n u + 1), if IsUnit (k : ZMod q) then w k else 0) /
          (q.totient : ℝ)| ≤ C * g u) ↔
    (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      ‖∑ k ∈ Finset.range (n u + 1), χ k * (w k : ℂ)‖ ≤ D * g u) := by
  classical
  let R (a : ZMod q) (u : ℕ) := ∑ k ∈ Finset.range (n u+1), if (k : ZMod q) = a then w k else 0
  let P (u : ℕ) := ∑ k ∈ Finset.range (n u+1), if IsUnit (k : ZMod q) then w k else 0
  let V (a : ZMod q) (u : ℕ) : ℂ := (R a u : ℂ) - (P u : ℂ)/(q.totient : ℂ)
  let T (χ : DirichletCharacter ℂ q) (u : ℕ) := ∑ k ∈ Finset.range (n u+1), χ k * (w k : ℂ)
  have hp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hn : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hV (a : ZMod q) (u : ℕ) : ‖V a u‖ = |R a u - P u/(q.totient : ℝ)| := by
    have he : V a u = ((R a u - P u/(q.totient : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  have principal (u : ℕ) : T 1 u = (P u : ℂ) := by
    simp only [T, P, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · simp [MulChar.one_apply h]
    · simp [MulChar.map_nonunit _ h]
  have forward (χ : DirichletCharacter ℂ q) (u : ℕ) :
      T χ u = ∑ b : ZMod q, χ b * (R b u : ℂ) := by
    simp only [T,R,Complex.ofReal_sum, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)))]
    apply Finset.sum_congr rfl
    intro k _
    simp [apply_ite Complex.ofReal, mul_ite]
  have inverse (a : ZMod q) (ha : IsUnit a) (u : ℕ) :
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * T χ u) = (q.totient : ℂ) * (R a u : ℂ) := by
    simp only [T,R,Complex.ofReal_sum,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, kernel q _ _ ha]
    by_cases hk : a = (k : ZMod q)
    · simp [hk]
    · simp [hk, Ne.symm hk]
  have cent (a : ZMod q) (ha : IsUnit a) (u : ℕ) :
      (q.totient : ℂ) * V a u =
        ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ a⁻¹ * T χ u := by
    have hsplit : (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * T χ u) =
        (P u : ℂ) + ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ a⁻¹ * T χ u := by
      calc
        _ = ∑ χ : DirichletCharacter ℂ q, ((if χ = 1 then (P u : ℂ) else 0) +
            (if χ = 1 then 0 else χ a⁻¹ * T χ u)) := by
          apply Finset.sum_congr rfl
          intro χ _
          by_cases h : χ = 1
          · subst χ
            have hai : IsUnit a⁻¹ := by
              obtain ⟨v,rfl⟩ := ha
              rw [ZMod.inv_coe_unit]
              exact Units.isUnit _
            simp [principal, MulChar.one_apply hai]
          · simp [h]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    calc
      _ = (q.totient : ℂ) * (R a u : ℂ) - (P u : ℂ) := by dsimp [V]; field_simp
      _ = _ := by rw [← inverse a ha u, hsplit]; abel
  change (∀ a, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |R a u-P u/(q.totient:ℝ)| ≤ C*g u) ↔
    (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ u, ‖T χ u‖ ≤ D*g u)
  constructor
  · intro h χ hχ
    have hzero (u : ℕ) : T χ u = ∑ b : ZMod q, χ b * V b u := by
      simp only [V,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,
        χ.sum_eq_zero_of_ne_one hχ,zero_mul,sub_zero,← forward]
    obtain ⟨D,hD,hd⟩ := bounded_finite_sum (fun b u => χ b * V b u) g (fun b => by
      by_cases hb : IsUnit b
      · obtain ⟨C,hC,hu⟩ := h b hb
        refine ⟨C,hC,fun u => ?_⟩
        rw [norm_mul]
        have z := mul_le_mul_of_nonneg_right (χ.norm_le_one b) (norm_nonneg (V b u))
        simpa only [one_mul,hV] using z.trans (by simpa only [one_mul,hV] using hu u)
      · exact ⟨0, le_rfl, fun u => by simp [χ.map_nonunit hb]⟩)
    exact ⟨D,hD,fun u => by rw [hzero]; exact hd u⟩
  · intro h a ha
    obtain ⟨D,hD,hd⟩ := bounded_finite_sum
      (fun (χ : DirichletCharacter ℂ q) u => if χ=1 then 0 else χ a⁻¹ * T χ u) g (fun χ => by
        by_cases hχ : χ=1
        · exact ⟨0,le_rfl,fun u => by simp [hχ]⟩
        · obtain ⟨C,hC,hu⟩ := h χ hχ
          refine ⟨C,hC,fun u => ?_⟩
          rw [if_neg hχ,norm_mul]
          have z := mul_le_mul_of_nonneg_right (χ.norm_le_one a⁻¹) (norm_nonneg (T χ u))
          exact (by simpa only [one_mul] using z : ‖χ a⁻¹‖ * ‖T χ u‖ ≤ ‖T χ u‖).trans (hu u))
    refine ⟨D/(q.totient : ℝ),div_nonneg hD hp.le,fun u => ?_⟩
    have z := hd u
    rw [← cent a ha u, norm_mul, Complex.norm_natCast, hV] at z
    calc
      _ ≤ D*g u/(q.totient : ℝ) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using z)
      _ = _ := by ring
