-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_indep_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:51.918181+00:00
-- url     : https://prove2.me/submissions/03cf5bbc-a226-4775-aeb6-6e29d0b17fc3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_idxE_can

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {K : Type} [CommRing K] {M : GLMod n} (CF : ColFam M) {ι' : Type} (e : ι' ≃ M.ι) (ε : ℤ)
    (h : ∀ nu : Fin n → ℤ, LinearIndependent K
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)))
    (nu : Fin n → ℤ) : LinearIndependent K
      (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) := by
  have hj : ∀ j : {j : CF.J // qc_sh (CF.mu j) ε = nu}, CF.mu j.1 = qc_sh nu (-ε) := by
    intro j
    funext a
    have := congrFun j.2 a
    simp only [qc_sh] at this ⊢
    omega
  have h1 := ((h (qc_sh nu (-ε))).map' (LinearEquiv.funCongrLeft K K e).toLinearMap (LinearEquiv.ker _)).comp
    (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)}))
    (fun j j' hjj => Subtype.ext (congrArg (fun x => x.1) hjj))
  have h2 : (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) =
      ((⇑(LinearEquiv.funCongrLeft K K e).toLinearMap ∘
        fun (j : {j : CF.J // CF.mu j = qc_sh nu (-ε)}) i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)) ∘
        fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)})) := by
    funext j i'
    simp only [qc_idxE_can]
    rfl
  rw [h2]
  exact h1
end Formalism.InvariantFactorPaths.ColumnFamilies
