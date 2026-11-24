-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.mem_bId_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:52.786033+00:00
-- url     : https://prove2.me/submissions/a51c32e4-359d-4675-9045-d0b5f7803ffb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_bot_of_max
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_valF_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution {n : 𝓞 F} (hn : n ≠ 0) (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    n ∈ bId v ↔ v ≤ valF n := by
  unfold bId Finsupp.prod
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime v.support (fun 𝔭 => 𝔭.1) v
    (fun 𝔭 _ => Ideal.prime_of_isPrime (ne_bot_of_max 𝔭.2) 𝔭.2.isPrime)
    (fun 𝔭 _ 𝔮 _ h => fun h' => h (Subtype.ext h')), Submodule.mem_finsetInf]
  constructor
  · intro h 𝔭
    by_cases h𝔭 : 𝔭 ∈ v.support
    · rw [valF_apply hn]
      exact (mem_pow_iff_le_vF 𝔭.2 hn _).mp (h 𝔭 h𝔭)
    · rw [Finsupp.notMem_support_iff.mp h𝔭]; exact Nat.zero_le _
  · intro h 𝔭 _
    have := h 𝔭
    rw [valF_apply hn] at this
    exact (mem_pow_iff_le_vF 𝔭.2 hn _).mpr this
end Formalism.HermitianLattices.Ext.L3.A5
