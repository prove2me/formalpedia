-- Prove2me | solution 1 for Formalism.L2.G.finite_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:31.135854+00:00
-- url     : https://prove2.me/submissions/31f02ca6-dca3-4478-a1e6-6295f1562817

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable (F : Type) [Field F] [NumberField F]
namespace Formalism.L2.G
theorem _root_.solution (g : ℕ) (hg : g ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((g : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
end Formalism.L2.G
