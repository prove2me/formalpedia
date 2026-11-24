-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.mem_one_of_locR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:55.512379+00:00
-- url     : https://prove2.me/submissions/7852bf5c-dad1-455f-be72-8e764fe5bb32

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_hcompl_le_primeCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution {x : K} (hx : ∀ p : Ideal (𝓞 K), p.IsMaximal → x ∈ locR (K := K) p) :
    x ∈ (1 : Submodule (𝓞 K) K) := by
  let J : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K x)
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hsx⟩ := hx p hp
    have hsJ : s ∈ J := by
      show LinearMap.toSpanSingleton (𝓞 K) K x s ∈ (1 : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply]
      exact hsx
    exact hcompl_le_primeCompl hp hs (hJp hsJ)
  have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
  change LinearMap.toSpanSingleton (𝓞 K) K x 1 ∈ (1 : Submodule (𝓞 K) K) at h1
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at h1
end Formalism.MainNotions.BridgeLemVR
