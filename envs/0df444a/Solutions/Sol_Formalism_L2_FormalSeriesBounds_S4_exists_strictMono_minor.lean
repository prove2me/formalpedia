-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.exists_strictMono_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:57:02.854737+00:00
-- url     : https://prove2.me/submissions/6bff2e94-4c83-48d0-a472-b218f84f6d34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) {n h : ℕ}
    (B : Matrix (Fin n) (Fin h) R) (g : Fin n → Fin h) (hg : (B.submatrix id g).det ≠ 0) :
    ∃ f : Fin n → Fin h, StrictMono f ∧ v (B.submatrix id f).det = v (B.submatrix id g).det := by
  have hinj : Function.Injective g := by
    by_contra hni
    apply hg
    simp only [Function.Injective, not_forall, exists_prop] at hni
    obtain ⟨i, j, hij, hne⟩ := hni
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])
  have hcard : (Finset.univ.image g).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  let f := (Finset.univ.image g).orderEmbOfFin hcard
  have hmem : ∀ i, f i ∈ Finset.univ.image g := fun i => Finset.orderEmbOfFin_mem _ hcard i
  choose σ hσ using fun i => Finset.mem_image.mp (hmem i)
  have hσinj : Function.Injective σ := fun a b hab =>
    f.injective (by rw [← (hσ a).2, ← (hσ b).2, hab])
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  refine ⟨f, f.strictMono, ?_⟩
  have hfe : B.submatrix id f = (B.submatrix id g).submatrix id τ := by
    ext a b
    simp [τ, (hσ b).2]
  rw [hfe, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1 <;> simp [h1]
end Formalism.L2.FormalSeriesBounds.S4
