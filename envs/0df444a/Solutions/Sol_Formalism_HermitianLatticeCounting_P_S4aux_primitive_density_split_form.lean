-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.primitive_density_split_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:07.241113+00:00
-- url     : https://prove2.me/submissions/d67f9a58-6360-49f8-b0a7-09b00e3e90cf

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fiber_card
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_li_count
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_density_arith
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : PrimDensitySplitForm := by
  intro K _ _ n m Ph Gm hn hPh
  classical
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hqpos : 0 < Fintype.card K := Fintype.card_pos

  let MX : (Fin m → Fin n → K) → Matrix (Fin m) (Fin n) K := fun X => (Matrix.of X) * Ph
  have hcond : ∀ (X Y : Fin m → Fin n → K),
      (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, (MX X).mulVec (Y j) = fun i => Gm i j := by
    intro X Y
    have : ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = (MX X).mulVec (Y j) i := by
      intro i j
      simp only [MX, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
      exact Finset.sum_comm
    simp only [this]
    constructor
    · intro h j; funext i; exact h i j
    · intro h i j; exact congrFun (h j) i
  have hrow : ∀ X : Fin m → Fin n → K, LinearIndependent K X → LinearIndependent K (MX X).row := by
    intro X hX
    have hinj : LinearMap.ker (Matrix.vecMulLinear Ph) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      have h1 : ∀ z : Fin n → K, Matrix.vecMul (Matrix.vecMul z Ph) Ph⁻¹ = z := fun z => by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv Ph hPh, Matrix.vecMul_one]
      rw [← h1 x, ← h1 y]
      exact congrArg (fun z => Matrix.vecMul z Ph⁻¹) hxy
    have := hX.map' (Matrix.vecMulLinear Ph) hinj
    have heq : (MX X).row = ⇑(Matrix.vecMulLinear Ph) ∘ X := by
      funext i
      funext l
      simp [MX, Matrix.row, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [heq]
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c * Fintype.card K ^ m = Fintype.card K ^ n :=
    ⟨Fintype.card K ^ (n - m), by rw [← pow_add]; congr 1; omega⟩
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hc
      exact absurd hc.symm (by positivity)
    · exact h
  let NY : (Fin m → Fin n → K) → ℕ := fun X =>
    (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j).card
  have hNY : ∀ X, LinearIndependent K X → ((NY X : ℕ) : ℝ) ≤ (c : ℝ) ^ m ∧
      (c : ℝ) ^ m - (Fintype.card K : ℝ) ^ m * (c : ℝ) ^ m / c ≤ ((NY X : ℕ) : ℝ) := by
    intro X hX
    let Fs : Fin m → Finset (Fin n → K) := fun j => univ.filter fun y => (MX X).mulVec y = fun i => Gm i j
    have hFs : ∀ j, (Fs j).card = c := by
      intro j
      have := fiber_card (MX X) (hrow X hX) (fun i => Gm i j)
      rw [← hc] at this
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    have heq : (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧
        ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j)
        = (Fintype.piFinset Fs).filter fun Y => LinearIndependent K Y := by
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Fs, hcond]
      exact and_comm
    have := li_count Fs c hFs hc0
    simp only [NY, heq]
    exact this
  have hXcount := li_count (F := K) (m := m) (n := n) (fun _ => univ) (Fintype.card K ^ n)
    (fun _ => by simp) (by positivity)
  have hpi : (Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n → K))) = univ := by
    ext; simp
  rw [hpi] at hXcount
  have hset : ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
      LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard : ℝ)
      = ∑ X ∈ univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X), ((NY X : ℕ) : ℝ) := by
    have h1 : {XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}
        = ↑(univ.filter fun XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) => LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j) := by
      ext; simp
    rw [h1, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases hX : LinearIndependent K X
    · simp only [hX, true_and, if_true, NY, Finset.card_filter]
      push_cast
      rfl
    · simp [hX]
  rw [hset]
  push_cast at hXcount
  refine density_arith (Fintype.card K : ℝ) hq2 n m hn (c : ℝ)
    ((univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X)).card : ℝ) _
    (by exact_mod_cast hc) hXcount.1 hXcount.2 ?_ ?_
  · rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).1
  · rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).2
end Formalism.HermitianLatticeCounting.P.S4aux
