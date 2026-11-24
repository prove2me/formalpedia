-- Prove2me | solution 1 for Formalism.UG.P.afsplitU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:10.712231+00:00
-- url     : https://prove2.me/submissions/64fdfa8c-e648-4293-97ea-2e43f58cb665

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Theorems.Thm_Formalism_UG_P_afsplitC_cT
import Theorems.Thm_Formalism_UG_P_afsplitC_J
import Theorems.Thm_Formalism_UG_P_afsplitU_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (h : GL n Rv) (k : GL n R)
    (hh : h ∈ UPts σ J (v.adicCompletion F)) (hk : k ∈ UPts σ J 𝔸) :
    afsplitU v h k ∈ UPts σ J 𝔸 := by
  unfold UPts UJ at hh hk ⊢
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hh hk ⊢
  rw [afsplitU_coe]
  conv_lhs => rw [afsplitC_J v J]
  rw [afsplitC_cT, afsplitC_mul, afsplitC_mul, hh, hk, ← afsplitC_J]
end Formalism.UG.P
