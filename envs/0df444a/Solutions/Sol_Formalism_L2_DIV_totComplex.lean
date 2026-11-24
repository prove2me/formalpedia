-- Prove2me | solution 1 for Formalism.L2.DIV.totComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:32.173858+00:00
-- url     : https://prove2.me/submissions/79c8ece9-2c0b-4b14-a86c-65737c12c13d

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_conj_ne_of_sq_neg
import Theorems.Thm_Formalism_L2_DIV_exists_sqrt
import Theorems.Thm_Formalism_L2_DIV_sqrts_sub
import Theorems.Thm_Formalism_L2_DIV_CoF_val_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : TotComplex := by
  intro ι LL d hd hK
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  obtain ⟨x, hx⟩ := exists_sqrt (-(d : ℤ))
  have hxL : x ∈ LL := hK (sqrts_sub _ hx)
  set y : CoF ι LL := CoF.mk ι LL x hxL with hy
  have hy2 : y ^ 2 = ((-(d : ℤ) : ℤ) : CoF ι LL) := by
    apply CoF.val_injective ι LL
    rw [map_pow, CoF.val_mk, map_intCast]
    exact hx
  have h2 : (v.embedding y) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ) := by
    rw [← map_pow, hy2, map_intCast]; push_cast; ring
  have hneg : (-(d : ℝ)) < 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  exact conj_ne_of_sq_neg hneg h2 (RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hreal) y)
end Formalism.L2.DIV
