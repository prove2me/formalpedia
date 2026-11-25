-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.unit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:37.687713+00:00
-- url     : https://prove2.me/submissions/78497a22-1b89-4b65-b91a-0f4097cb55b6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_hb_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_alg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_apply
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_det_ne_zero_of_chars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} {n : ℕ} (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (t : Fin n ≃ EmbX (R := R) e) (jj : ZMod d ≃ Fin n)
    (ht : ∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) :
    IsUnit (Matrix.det (Matrix.of fun i j =>
      tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE))) := by
  have hdet := det_ne_zero_of_chars (F := ℤ_[l]) (fun j => chi (l := l) ((t j : EmbX (R := R) e) : OE →+* R))
    (by
      intro j j' h
      obtain ⟨a, rfl⟩ := jj.surjective j
      obtain ⟨a', rfl⟩ := jj.surjective j'
      simp only [ht] at h
      rw [chi_inj em hsep h])
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun j r => chi_alg _ r) e
    (fun j => by rw [chi_apply, (t j).2, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  by_contra hu
  apply hdet
  have h1 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
  rw [RingHom.map_det] at h1
  exact h1
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
