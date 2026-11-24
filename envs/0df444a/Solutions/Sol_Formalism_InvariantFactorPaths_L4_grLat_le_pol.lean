-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.grLat_le_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:16.578921+00:00
-- url     : https://prove2.me/submissions/6c809088-0e2c-41fd-9192-fef88a5cbe64

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfM : f ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hfP : f ∈ Pol p r LLw :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1
  show initPart v e f ∈ Pol p r LLw
  unfold Pol at hfP ⊢
  rw [mem_restrictSupport_iff] at hfP ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart] at hm
  refine hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
  intro h0
  apply hm
  rw [h0, ite_self]
end Formalism.InvariantFactorPaths.L4
