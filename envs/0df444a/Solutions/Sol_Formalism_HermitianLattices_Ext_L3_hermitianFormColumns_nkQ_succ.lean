-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.nkQ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:41.571324+00:00
-- url     : https://prove2.me/submissions/d49d6398-2c91-483b-8cd2-8fbd54b7cf18

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_card_vec_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_fm_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_fm_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_piQ
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_solve_scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) {c k : ℕ} (hk : 2 * c + 1 ≤ k) :
    nkQ 𝔭 (k + 1) c H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n := by
  have hF : IsFixF K F := Fact.out
  have hck : c + 1 ≤ k := by omega
  have hj : k + 1 ≤ 2 * (k - c) := by omega
  have hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) →
      (Qc 𝔭 k c H (fun i => mkk K 𝔭 k ((x + y) i)) ↔ Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i))) := by
    intro x y hy
    rw [Qc_mk hck H, Qc_mk hck H]
    have hy' : ∀ j', (star y ᵥ* H) j' ∈ extP K 𝔭 ^ (c + 1) := fun j' =>
      Ideal.pow_le_pow_right (by omega)
        (vecMul_mem (fun a => conjO_mem_pow hF 𝔭 (k - c) _ (hy a)) H j')
    have e : ∀ j', (star (x + y) ᵥ* H) j' = (star x ᵥ* H) j' + (star y ᵥ* H) j' := by
      intro j'
      rw [star_add, Matrix.add_vecMul]
      rfl
    simp only [e]
    constructor
    · rintro ⟨j', hj'⟩
      exact ⟨j', fun h => hj' (Ideal.add_mem _ h (hy' j'))⟩
    · rintro ⟨j', hj'⟩
      refine ⟨j', fun h => hj' ?_⟩
      have h2 := Ideal.sub_mem _ h (hy' j')
      simpa using h2
  have RC : ∀ x : m → 𝓞 K, Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) →
      fm H x x - ι n ∈ extP K 𝔭 ^ k → ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) ∧
        fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1) := by
    intro x hQ _ s hs hs'
    obtain ⟨j0, hj0⟩ := (Qc_mk hck H x).mp hQ
    obtain ⟨r, hr, hr'⟩ := exists_solve_scalar hK hF h𝔭 (by omega : c ≤ k) hj0 hs hs'
    refine ⟨Pi.single j0 r, fun a => ?_, ?_⟩
    · by_cases ha : a = j0
      · subst ha
        simpa using hr
      · simp [Pi.single_apply, ha]
    · have e1 : fm H x (Pi.single j0 r) = (star x ᵥ* H) j0 * r := by
        rw [fm_eq]
        first
        | exact dotProduct_single _ _ _
        | simp [dotProduct, Pi.single_apply]
      rw [fm_star hH x (Pi.single j0 r), e1]
      exact hr'
  have h := card_vec_succ hK h𝔭 H hH n hj (Qc 𝔭 k c H) hinv RC
  have e : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) //
      Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} = nkQ 𝔭 (k + 1) c H n :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Qc_piQ hck H x]))
  rw [e] at h
  exact h
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
