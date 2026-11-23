-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.len_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:16.503793+00:00
-- url     : https://prove2.me/submissions/013804c9-e955-4a9b-9252-c417faf8f933

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Theorems.Thm_P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_len_zero_of_le
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
namespace Formalism.DivisionValues.LocalCovolumeBasis
theorem _root_.solution {N : Submodule (𝓞 K) V} {a : V} {p : Ideal (𝓞 K)} (hpmax : p.IsMaximal)
    (hp : ∀ r, r ∈ p ↔ r • a ∈ N) (q : Ideal (𝓞 K)) [hq : q.IsPrime] (hqmax : q ≠ ⊤)
    (hqp : q ≠ p) :
    Module.length (𝓞 K) (↥(localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})) ⧸
      (localization₂ q N).comap (localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})).subtype) = 0 := by
  apply len_zero_of_le
  have : ∃ s ∈ p, s ∉ q := by
    by_contra hcon
    push Not at hcon
    exact hqp (hpmax.eq_of_le hqmax hcon).symm
  obtain ⟨s, hsp, hsq⟩ := this
  intro x hx
  obtain ⟨t, htq, htx⟩ := (mem_locP' q _ x).mp hx
  refine (mem_locP' q N x).mpr ⟨s * t, fun h => (hq.mem_or_mem h).elim hsq htq, ?_⟩
  rw [mul_smul]
  exact kill hp hsp htx
end Formalism.DivisionValues.LocalCovolumeBasis
