-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:41.19532+00:00
-- url     : https://prove2.me/submissions/14f80cf6-f9a4-4ebc-8ff2-e3afb4c93a87

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis

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
theorem _root_.solution {N : Submodule (𝓞 K) V} {a : V} {p : Ideal (𝓞 K)} (hp : ∀ r, r ∈ p ↔ r • a ∈ N)
    {s : 𝓞 K} (hs : s ∈ p) {y : V} (hy : y ∈ N ⊔ Submodule.span (𝓞 K) {a}) : s • y ∈ N := by
  obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [smul_add, smul_smul]
  exact N.add_mem (N.smul_mem s hn) ((hp _).mp (Ideal.mul_mem_right c p hs))
end Formalism.DivisionValues.LocalCovolumeBasis
