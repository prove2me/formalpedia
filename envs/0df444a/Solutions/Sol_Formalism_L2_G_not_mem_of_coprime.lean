-- Prove2me | solution 1 for Formalism.L2.G.not_mem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:18.130173+00:00
-- url     : https://prove2.me/submissions/e2c768cc-9340-4056-b68b-9809a9984bee

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGLev

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
namespace Formalism.L2.G
theorem _root_.solution {p g : ℕ} (h : Nat.Coprime p g) (v : HeightOneSpectrum (𝓞 F))
    (hg : ((g : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have h1 : ((a * p + b * g : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hg)
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end Formalism.L2.G
