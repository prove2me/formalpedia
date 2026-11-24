-- Prove2me | solution 1 for Formalism.L2.G.congChar_princ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:37.128145+00:00
-- url     : https://prove2.me/submissions/85121a7d-0d26-49f7-ba20-575ff4253264

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Theorems.Thm_Formalism_L2_G_congChar_apply

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
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G
theorem _root_.solution {Z : Type} [Group Z] (ι : R →+* A) (hι : Function.Injective ι) (I : Ideal R)
    (H : Subgroup (GL n (R ⧸ I))) (lam : H →* Z) (x : congPre ι I H) (hx : (x : GL n A) ∈ princ ι I) :
    congChar ι hι I H lam x = 1 := by
  obtain ⟨g, hg, hgx⟩ := hx
  have hg1 : redGL I g = 1 := hg
  have hgH : redGL I g ∈ H := by rw [hg1]; exact H.one_mem
  have hm : bc ι g ∈ congPre ι I H := hgx ▸ x.2
  have hx' : x = ⟨bc ι g, hm⟩ := Subtype.ext hgx.symm
  rw [hx', congChar_apply ι hι I H lam g hgH hm]
  have : (⟨redGL I g, hgH⟩ : H) = 1 := Subtype.ext hg1
  rw [this, map_one]
end Formalism.L2.G
