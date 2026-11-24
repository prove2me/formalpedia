-- Prove2me | solution 1 for Formalism.UG.P.split_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:52.80574+00:00
-- url     : https://prove2.me/submissions/1452c137-814e-4dfa-98a3-0cc382a57e19

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
import Theorems.Thm_Formalism_UG_P_split_mat_ext
import Theorems.Thm_Formalism_UG_P_split_map_fst_mul
import Theorems.Thm_Formalism_UG_P_split_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by
  have hF : (g : Matrix n n (R × R)).map Prod.fst * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst = 1 := by
    rw [← split_map_fst_mul, Units.mul_inv]
    exact Matrix.map_one _ rfl rfl
  have e1 := (split_mem_iff J₁ g).mp hg
  have e2 := (split_mem_iff J₁ g').mp hg'
  rw [← h] at e2
  have k1 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1]
  have k2 : ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e2]
  have k3 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ := by
    have h3 := congrArg (fun M : Matrix n n R => M * J₁⁻¹) (k1.trans k2.symm)
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] using h3
  have k4 := congrArg Matrix.transpose k3
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at k4
  exact Units.ext (split_mat_ext h k4)
end Formalism.UG.P
