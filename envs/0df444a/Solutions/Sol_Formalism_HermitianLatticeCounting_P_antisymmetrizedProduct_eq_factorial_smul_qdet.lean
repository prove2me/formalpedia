-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:04.074862+00:00
-- url     : https://prove2.me/submissions/811ff7c3-b0e9-4bb7-92c3-bc78eefa61f0

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_REAL_quantumMinor_adjacent_col_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by

  have hcol : ∀ (b : Fin n → Fin n) (τ : Equiv.Perm (Fin n)),
      qminor E id (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E id b u := by
    cases n with
    | zero =>
      intro b τ
      rw [Subsingleton.elim τ 1]
      simp
    | succ m =>
      intro b τ
      have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      revert b
      induction hτ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro b
        rw [quantumMinor_adjacent_col_swap E hE id b i u, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
        simp
      | one =>
        intro b
        simp
      | mul x y _ _ hx hy =>
        intro b
        show qminor E id ((b ∘ x) ∘ y) u = _
        rw [hy (b ∘ x), hx b]
        simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc]
        congr 1
        exact (Int.cast_commute _ _).eq
  simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
  have hin : ∀ τ : Equiv.Perm (Fin n), ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
      orderedTermProduct E (fun k => u - (k : ℂ)) σ τ = qminor E id (id ∘ τ) u := fun τ => rfl
  have hsq : ∀ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign τ : ℤ) : A) * qminor E id id u) = qminor E id id u := by
    intro τ
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one,
      one_mul]
  simp only [hin, hcol, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rfl
end Formalism.HermitianLatticeCounting.P
