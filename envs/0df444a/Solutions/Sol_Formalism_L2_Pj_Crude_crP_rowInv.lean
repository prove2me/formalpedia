-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_rowInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:56.276346+00:00
-- url     : https://prove2.me/submissions/52e580b3-54de-49aa-9670-89aeefd66213

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crSig_iff

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    RowInv r n k (crP r n k β a) := by
  unfold RowInv rowShift
  intro σ i i' hii' t
  have hlt : (i' : ℕ) < i := hii'
  unfold crP
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun kk _ => ?_
  rw [map_pow, AlgHom.map_det]
  congr 1
  by_cases hcase : τ = σ ∧ (i : ℕ) ≤ kk
  · obtain ⟨rfl, hik⟩ := hcase
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin ((kk : ℕ) + 1), (i₀ : ℕ) = i := ⟨⟨i, by omega⟩, rfl⟩
    obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin ((kk : ℕ) + 1), (i₁ : ℕ) = i' := ⟨⟨i', by omega⟩, rfl⟩
    have hne : i₀ ≠ i₁ := by
      intro h
      subst h
      omega
    conv_rhs => rw [← Matrix.det_updateRow_add_smul_self _ hne (C t)]
    congr 1
    ext p q
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, crMinor, aeval_X, Matrix.updateRow_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, crSig_iff]
    by_cases hp : p = i₀
    · subst hp
      have h1 : Fin.castLE kk.isLt p = i := Fin.ext (by simp [hi₀])
      have h2 : Fin.castLE kk.isLt i₁ = i' := Fin.ext (by simp [hi₁])
      simp [h1, h2]
    · have h1 : Fin.castLE kk.isLt p ≠ i := by
        intro h
        apply hp
        have h4 := congrArg Fin.val h
        simp at h4
        exact Fin.ext (by omega)
      simp [h1, hp]
  · congr 1
    ext p q
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, crMinor, aeval_X]
    rw [if_neg]
    rintro ⟨b, hb⟩
    apply hcase
    obtain ⟨h1, h2⟩ := Sigma.mk.inj hb
    refine ⟨h1, ?_⟩
    subst h1
    have h3 := (Prod.mk.inj (eq_of_heq h2)).1
    have h4 := congrArg Fin.val h3
    have hp := p.isLt
    simp at h4
    omega
end Formalism.L2.Pj.Crude
