-- Prove2me | solution 1 for FoundationsML.Kernels.RKHS_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:33:39.031403+00:00
-- url     : https://prove2.me/submissions/ffb1b1a8-d340-4040-af4d-893b5143c281

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf

set_option autoImplicit false

namespace P55340e55

open FoundationsML.Kernels in
/-- The semi-inner product `⟨f, g⟩ = ∑_{y,x} f y * g x * K y x` on finitely supported functions. -/
noncomputable def kcore {X : Type} (K : X → X → ℝ) (hK : IsPDS K) :
    PreInnerProductSpace.Core ℝ (X →₀ ℝ) where
  inner f g := f.sum fun y a => g.sum fun x b => a * b * K y x
  conj_inner_symm f g := by
    simp only [conj_trivial]
    rw [Finsupp.sum_comm]
    refine Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun x _ => ?_
    rw [hK.1 x y]; ring
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    exact hK.2 f.support f
  add_left f f' g := by
    rw [Finsupp.sum_add_index']
    · intro y; simp
    · intro y a₁ a₂
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun x _ => ?_
      ring
  smul_left f g r := by
    simp only [conj_trivial]
    rw [Finsupp.sum_smul_index']
    · rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x _ => ?_
      simp only [smul_eq_mul]; ring
    · intro y; simp

end P55340e55

open FoundationsML.Kernels in
theorem solution {X : Type} (K : X → X → ℝ) (hK : IsPDS K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (Φ : X → H) (ev : H → X → ℝ), IsRKHSOf K Φ ev := by
  letI c : PreInnerProductSpace.Core ℝ (X →₀ ℝ) := P55340e55.kcore K hK
  letI : SeminormedAddCommGroup (X →₀ ℝ) :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ (X →₀ ℝ) := InnerProductSpace.ofCore c
  refine ⟨UniformSpace.Completion (X →₀ ℝ), inferInstance, inferInstance, inferInstance,
    fun x => ((Finsupp.single x (1 : ℝ) : X →₀ ℝ) : UniformSpace.Completion (X →₀ ℝ)),
    fun h x => inner ℝ h ((Finsupp.single x (1 : ℝ) : X →₀ ℝ) : UniformSpace.Completion (X →₀ ℝ)),
    ?_, ?_⟩
  · intro x x'
    rw [UniformSpace.Completion.inner_coe]
    show K x x' = (Finsupp.single x (1 : ℝ)).sum fun y a =>
      (Finsupp.single x' (1 : ℝ)).sum fun z b => a * b * K y z
    simp
  · intro h x
    rfl
