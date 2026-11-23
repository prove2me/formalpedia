-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.back
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:29.311622+00:00
-- url     : https://prove2.me/submissions/cfdec1a0-9161-45e6-bd43-ecf1c39bbd1a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_finsum_if

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution {cr : K ⧸ R.toAddSubgroup → Kˣ} {S : Set K} (t₁ : Kˣ)
    (hSfin : {x | (cr x : K) ∈ S}.Finite) (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    {i1 : DecidablePred fun x => (cr x : K) ∈ S}
    {i2 : ∀ x, DecidablePred fun z : Kˣ => z ^ (m + 1) = (-t₁) ^ m * cr x} (G : Kˣ → ℂ) :
    ∑ᶠ x, (if (cr x : K) ∈ S then
      ∑ᶠ z : Kˣ, (if z ^ (m + 1) = (-t₁) ^ m * cr x then G z else 0) else 0) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset, G z := by
  rw [finsum_if hSfin]
  apply Finset.sum_congr rfl
  intro x _
  exact finsum_if (hroots _) G
end Formalism.FourierDecayAlt.P.GermSumLattices
