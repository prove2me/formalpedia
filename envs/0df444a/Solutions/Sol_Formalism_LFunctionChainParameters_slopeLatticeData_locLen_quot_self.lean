-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.locLen_quot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:31:56.964378+00:00
-- url     : https://prove2.me/submissions/c8564644-c873-4bc1-bd84-05e073aced40

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {R : Type} [CommRing R]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (m : Ideal R) [hm : m.IsMaximal] : locLen m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring
end Formalism.LFunctionChainParameters.slopeLatticeData
