-- Prove2me | solution 1 for FoundationsML.Kernels.representer_theorem_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:38:05.049006+00:00
-- url     : https://prove2.me/submissions/7c7052fa-13c4-41a7-8e84-ecdf80a546dc

/-
Mohri–Rostamizadeh–Talwalkar, Theorem 6.11 (Representer theorem), corrected reading.

For a minimizer `h` of `F h = G ‖h‖ + L (h x₁, …, h x_m)`, the orthogonal projection `h₁` of `h`
onto `span {Φ x_i}` takes the same values at the points `x_i` (reproducing property: the
difference is orthogonal to every `Φ x_i`), and `‖h₁‖ ≤ ‖h‖` with strict inequality when
`h ∉ span`.  Monotonicity of `G` gives `F h₁ ≤ F h`; strict monotonicity of `G` and finiteness of
`L` at the minimizer give `F h₁ < F h` unless `h = h₁`.
-/
import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf
import Definitions.Def_FoundationsML_Kernels_IsMinimizer

set_option autoImplicit false

namespace RepresenterProof

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The projection of `h` onto `span {Φ x_i}` is a combination of the `Φ x_i`, has the same inner
products with them, and is no longer than `h` (strictly shorter unless it equals `h`). -/
theorem proj_facts {m : ℕ} (Φ : X → H) (x : Fin m → X) (h : H) :
    ∃ h₁ : H, (∃ α : Fin m → ℝ, ∑ i, α i • Φ (x i) = h₁) ∧
      (∀ i, inner ℝ h₁ (Φ (x i)) = inner ℝ h (Φ (x i))) ∧ ‖h₁‖ ≤ ‖h‖ ∧
      (h₁ ≠ h → ‖h₁‖ < ‖h‖) := by
  classical
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range fun i => Φ (x i)) with hS
  have : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hP : S.starProjection h ∈ S := S.starProjection_apply_mem h
  have horth : h - S.starProjection h ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal h
  refine ⟨S.starProjection h, (Submodule.mem_span_range_iff_exists_fun ℝ).mp hP, ?_,
    Submodule.norm_starProjection_apply_le S h, ?_⟩
  · intro i
    have hmem : Φ (x i) ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have h0 := (Submodule.mem_orthogonal' S _).mp horth _ hmem
    rw [inner_sub_left] at h0
    linarith
  · intro hne
    have hin : inner ℝ (S.starProjection h) (h - S.starProjection h) = 0 :=
      (Submodule.mem_orthogonal S _).mp horth _ hP
    have hsq : ‖h‖ ^ 2 = ‖S.starProjection h‖ ^ 2 + ‖h - S.starProjection h‖ ^ 2 := by
      have := norm_add_sq_real (S.starProjection h) (h - S.starProjection h)
      rw [add_sub_cancel, hin] at this
      linarith
    have hpos : 0 < ‖h - S.starProjection h‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    by_contra hcon
    push Not at hcon
    nlinarith [mul_self_le_mul_self (norm_nonneg h) hcon, mul_pos hpos hpos]

end RepresenterProof

open FoundationsML.Kernels in
theorem solution
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (hK : IsPDS K) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev)
    (m : ℕ) (x : Fin m → X)
    (G : ℝ → ℝ) (hG : Monotone G)
    (L : (Fin m → ℝ) → WithTop ℝ)
    (F : H → WithTop ℝ) (hF : ∀ h : H, F h = (G ‖h‖ : WithTop ℝ) + L (fun i => ev h (x i))) :
    ((∃ h : H, IsMinimizer F h) → ∃ α : Fin m → ℝ, IsMinimizer F (∑ i, α i • Φ (x i))) ∧
    (StrictMono G → (∃ h₀ : H, F h₀ ≠ ⊤) →
      ∀ h : H, IsMinimizer F h → ∃ α : Fin m → ℝ, h = ∑ i, α i • Φ (x i)) := by
  -- the projection has the same point values as `h`
  have hvals : ∀ h h₁ : H, (∀ i, inner ℝ h₁ (Φ (x i)) = inner ℝ h (Φ (x i))) →
      (fun i => ev h₁ (x i)) = (fun i => ev h (x i)) := by
    intro h h₁ hin
    funext i
    rw [hRKHS.2, hRKHS.2]
    exact hin i
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hh⟩
    obtain ⟨h₁, ⟨α, hα⟩, hin, hn, -⟩ := RepresenterProof.proj_facts Φ x h
    have hle : F h₁ ≤ F h := by
      rw [hF h₁, hF h, hvals h h₁ hin]
      exact add_le_add_left (WithTop.coe_le_coe.mpr (hG hn)) _
    refine ⟨α, ?_⟩
    rw [hα]
    exact fun h' => hle.trans (hh h')
  · intro hGs ⟨h₀, h₀top⟩ h hh
    obtain ⟨h₁, ⟨α, hα⟩, hin, hn, hstrict⟩ := RepresenterProof.proj_facts Φ x h
    by_cases heq : h₁ = h
    · exact ⟨α, (hα.trans heq).symm⟩
    · exfalso
      have hlt : ‖h₁‖ < ‖h‖ := hstrict heq
      have hGlt : G ‖h₁‖ < G ‖h‖ := hGs hlt
      have hfin : F h ≠ ⊤ := fun htop => h₀top (top_le_iff.mp (htop ▸ hh h₀))
      have hLfin : L (fun i => ev h (x i)) ≠ ⊤ := by
        intro hL
        apply hfin
        rw [hF h, hL]
        simp
      obtain ⟨ℓ, hℓ⟩ := WithTop.ne_top_iff_exists.mp hLfin
      have h1 : F h₁ = ((G ‖h₁‖ + ℓ : ℝ) : WithTop ℝ) := by
        rw [hF h₁, hvals h h₁ hin, ← hℓ, WithTop.coe_add]
      have h2 : F h = ((G ‖h‖ + ℓ : ℝ) : WithTop ℝ) := by
        rw [hF h, ← hℓ, WithTop.coe_add]
      have h3 : F h₁ < F h := by
        rw [h1, h2]
        exact WithTop.coe_lt_coe.mpr (by linarith)
      exact absurd (hh h₁) (not_le.mpr h3)
