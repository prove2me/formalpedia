-- Prove2me | solution 1 for Formalism.UG.P.levelvsplit_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:56.117696+00:00
-- url     : https://prove2.me/submissions/5131b1b3-2fd9-4778-b90b-540b7943bbf7

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit

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
variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2
end Formalism.UG.P
