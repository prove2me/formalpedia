-- Prove2me | solution 1 for DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f886fb14-0143-5645-a856-462b586e328f

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Theorems.Thm_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose
import Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation

set_option autoImplicit false

universe u

namespace G1PSOL

open DoubleComplex

theorem main
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    Nonempty (DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (dA 0)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot D (n + 1) ≃ₗ[R]
        (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype)) := by
  classical

  have hex : ∀ p q : ℕ, Subsingleton (colH (transpose D) q (p + 1)) := by
    intro p q
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro z -
    show z ∈ colB (transpose D) q (p + 1)
    simp only [colB, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
    obtain ⟨b, hb⟩ := hrows p q z.2
    exact ⟨b, hb⟩

  let ψ : ∀ i : ℕ, colH (transpose D) i 0 ≃ₗ[R] A i := fun i =>
    (Submodule.quotEquivOfEqBot (colB (transpose D) i 0) rfl).trans
      ((LinearEquiv.ofEq (LinearMap.ker (D.dH 0 i)) (LinearMap.range (ε i)) (hker i)).trans
        (LinearEquiv.ofInjective (ε i) (hε i)).symm)
  have hkey : ∀ (i : ℕ) (w : LinearMap.range (ε i)),
      ε i ((LinearEquiv.ofInjective (ε i) (hε i)).symm w) = (w : D.C 0 i) := by
    intro i w
    conv_rhs => rw [← (LinearEquiv.ofInjective (ε i) (hε i)).apply_symm_apply w]
    rw [LinearEquiv.ofInjective_apply]
  have hψ : ∀ (i : ℕ) (z : LinearMap.ker ((transpose D).dV i 0)),
      ε i (ψ i (Submodule.Quotient.mk z)) = z.1 := by
    intro i z
    show ε i ((LinearEquiv.ofInjective (ε i) (hε i)).symm
      (LinearEquiv.ofEq _ _ (hker i) (Submodule.quotEquivOfEqBot (colB (transpose D) i 0) rfl
        (Submodule.Quotient.mk z)))) = _
    rw [Submodule.quotEquivOfEqBot_apply_mk, hkey]
    rfl
  have he : ∀ (i : ℕ) (x : colH (transpose D) i 0),
      ψ (i + 1) (colHdH (transpose D) i 0 x) = dA i (ψ i x) := by
    intro i x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply hε (i + 1)
    conv_rhs => rw [← LinearMap.comp_apply, ← hεd i, LinearMap.comp_apply, hψ]
    simp only [colHdH, Submodule.mapQ_apply]
    rw [hψ]
    rfl
  obtain ⟨h0, hS⟩ := LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (fun i => colHdH (transpose D) i 0) dA ψ he
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨e1⟩ := DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose D hex 0
    obtain ⟨e2⟩ := h0
    exact ⟨e1.trans ((Submodule.quotEquivOfEqBot _ rfl).trans e2)⟩
  · obtain ⟨e1⟩ := DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose D hex (n + 1)
    obtain ⟨e2⟩ := hS n
    exact ⟨e1.trans e2⟩

end G1PSOL

theorem solution
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    Nonempty (DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (dA 0)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot D (n + 1) ≃ₗ[R]
        (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype)) :=
  G1PSOL.main D A dA ε hε hεd hker hrows

end S_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation
end P2MW
export P2MW.S_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation (solution)
