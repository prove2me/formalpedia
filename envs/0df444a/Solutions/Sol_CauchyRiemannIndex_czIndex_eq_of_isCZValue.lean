-- Prove2me | solution 1 for CauchyRiemannIndex.czIndex_eq_of_isCZValue
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:16:20.784965+00:00
-- url     : https://prove2.me/submissions/f3111435-0378-4056-a38b-d9130ffc0bfc

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_ConleyZehnder_czValue_existsUnique

open Matrix

namespace CRModel

open CauchyRiemannIndex

noncomputable section

lemma czIndex_eq_of_isCZValue {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hSP : ψ ∈ ConleyZehnder.SP n) {k : ℤ} (hk : IsCZValue ψ k) : czIndex ψ = k := by
  obtain ⟨k', -, huniq⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (huniq _ hex.choose_spec).trans (huniq _ hk).symm

lemma czIndex_eq_of_isCZValue_aux {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hsymp : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0) (k : ℤ)
    (hk : IsCZValue ψ k) : czIndex ψ = k :=
  czIndex_eq_of_isCZValue ψ ⟨hsymp, h0, h1⟩ hk

end

end CRModel

open CauchyRiemannIndex

open Matrix

theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hsymp : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0) (k : ℤ)
    (hk : IsCZValue ψ k) : czIndex ψ = k :=
  CRModel.czIndex_eq_of_isCZValue_aux ψ hsymp h0 h1 k hk
