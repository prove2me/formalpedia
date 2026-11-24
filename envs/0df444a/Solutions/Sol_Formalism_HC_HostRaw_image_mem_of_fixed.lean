-- Prove2me | solution 1 for Formalism.HC.HostRaw.image_mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:59.342018+00:00
-- url     : https://prove2.me/submissions/ea671664-161d-4ca1-be7d-5211675c3316

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_HostRaw_emb_mem_adjoin_of_fixed
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb


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
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    J x ∈ M := by
  let _ : Algebra H.E (Cond.Cyc H.condN) := (emb H).toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) := IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm
  have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let _ : Algebra H.E Ω := J.toAlgebra
  let Ψ : Cond.Cyc H.condN →ₐ[H.E] Ω := IsAlgClosed.lift
  have h1 : Ψ (emb H x) = J x := Ψ.commutes x
  rw [← h1]
  have h2 := H.emb_mem_adjoin_of_fixed hm x hx
  generalize emb H x = z at h2
  induction h2 using adjoin_induction with
  | mem y hy => exact hM _ (by rw [← map_pow, show y ^ m = 1 from hy, map_one])
  | algebraMap r =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem M r
  | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact M.inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact M.mul_mem ha hb
end Formalism.HC.HostRaw
