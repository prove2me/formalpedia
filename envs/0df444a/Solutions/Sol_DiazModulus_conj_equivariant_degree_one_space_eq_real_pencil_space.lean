-- Prove2me | solution 1 for DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:06:38.012989+00:00
-- url     : https://prove2.me/submissions/9369ca0c-8c95-429d-a44e-3ed6c91a2b24

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A conjugation-equivariant degree-one space is a real pencil space

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, and `g` with `1, u, ū, g, ug` free over `Q̄` and
`ḡ = a + bu + c·ug` (`a, b, c ∈ Q̄`). Conjugating once more and substituting gives
`(1 − c c̄ s²) g = (ā + c̄ b s²) + (b̄ + c̄ a) ū`, so by independence of `1, ū, g` the three
coefficients vanish: `c c̄ s² = 1`, `ā = −c̄ b s²`, `b̄ = −c̄ a`. With `q = a/(c s²)` one has
`q̄ = −b`, and `g' = g + q ū` satisfies `conj g' = c u g'`. Put `λ = c s` (so `λ λ̄ = 1`) and
`f = g'(s + λu)`; then `f̄ = f`. Since `u ∉ Q̄`, `s + λu ≠ 0` and `f/(s + λu) = g'`. Finally
`Q̄ + Q̄u + Q̄ū + Q̄g + Q̄ug = Q̄ + Q̄u + Q̄ū + Q̄f + Q̄g'`, each generator of one side being an
explicit `Q̄`-combination of generators of the other (`g = g' − qū`,
`ug = λ⁻¹ f − λ⁻¹ s g' − q s²`, `f = s g + s q ū + λ ug + λ q s²`). -/

namespace R11_conjEquiv

open DiazModulus

theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

theorem mul_mem_span {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S :=
  Submodule.smul_mem _ (⟨c, hc⟩ : Qbar) hv

/-- `1, ū, g` are free over `Q̄`. -/
theorem indep3 {u g : ℂ} (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    {α β γ : ℂ} (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hγ : γ ∈ Qbar)
    (h : α + β * conj u + γ * g = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  have := Fintype.linearIndependent_iff.1 hind
    ![⟨α, hα⟩, 0, ⟨β, hβ⟩, ⟨γ, hγ⟩, 0] (by
      simp [Fin.sum_univ_five, Subfield.smul_def]
      linear_combination h)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val (this 0)
  · simpa using congrArg Subtype.val (this 2)
  · simpa using congrArg Subtype.val (this 3)

end R11_conjEquiv

open DiazModulus R11_conjEquiv in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) (g : ℂ)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    (hcg : conj g ∈ Submodule.span Qbar ({1, u, u * g} : Set ℂ)) :
    ∃ lam f : ℂ, lam ∈ Qbar ∧ lam * conj lam = 1 ∧ conj f = f ∧
      Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) = Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : u * conj u = 0 := by rw [← hss]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact hu0 h
    · exact hu0 (by simpa using h)
  obtain ⟨a', b', c', habc⟩ := Submodule.mem_span_triple.1 hcg
  have hcg' : conj g = (a' : ℂ) + (b' : ℂ) * u + (c' : ℂ) * (u * g) := by
    rw [← habc]; simp [Subfield.smul_def]
  have ha : (a' : ℂ) ∈ Qbar := a'.2
  have hb : (b' : ℂ) ∈ Qbar := b'.2
  have hc : (c' : ℂ) ∈ Qbar := c'.2
  generalize (a' : ℂ) = a at hcg' ha
  generalize (b' : ℂ) = b at hcg' hb
  generalize (c' : ℂ) = c at hcg' hc
  have h2 : g = conj a + conj b * conj u + conj c * (conj u * conj g) := by
    have := congrArg conj hcg'
    rw [Complex.conj_conj, map_add, map_add, map_mul, map_mul, map_mul] at this
    exact this
  rw [hcg'] at h2
  have hss' : s * s ∈ Qbar := Qbar.mul_mem hs hs
  obtain ⟨h_a, h_b, h_c⟩ := indep3 hind
    (Qbar.add_mem (conj_mem ha) (Qbar.mul_mem (Qbar.mul_mem (conj_mem hc) hb) hss'))
    (Qbar.add_mem (conj_mem hb) (Qbar.mul_mem (conj_mem hc) ha))
    (Qbar.sub_mem (Qbar.mul_mem (Qbar.mul_mem hc (conj_mem hc)) hss') Qbar.one_mem)
    (show (conj a + conj c * b * (s * s)) + (conj b + conj c * a) * conj u
        + (c * conj c * (s * s) - 1) * g = 0 by
      linear_combination (-1 : ℂ) * h2 + (conj c * b + c * conj c * g) * hss)
  have hc0 : c ≠ 0 := by intro h; rw [h] at h_c; simp at h_c
  have hcc0 : conj c ≠ 0 := by simpa using hc0
  obtain ⟨q, hq_def⟩ : ∃ q : ℂ, q = a / (c * (s * s)) := ⟨_, rfl⟩
  have hq : q ∈ Qbar := hq_def ▸ Qbar.div_mem ha (Qbar.mul_mem hc hss')
  have hcq : c * q * (s * s) = a := by rw [hq_def]; field_simp
  have hconjq : conj q = -b := by
    rw [hq_def, map_div₀, map_mul, map_mul, hsr, div_eq_iff (mul_ne_zero hcc0 (mul_ne_zero hs0 hs0))]
    linear_combination h_a
  obtain ⟨g', hg'_def⟩ : ∃ g' : ℂ, g' = g + q * conj u := ⟨_, rfl⟩
  have hg'conj : conj g' = c * u * g' := by
    rw [hg'_def, map_add, map_mul, Complex.conj_conj, hcg', hconjq]
    linear_combination (c * q) * hss - hcq
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℂ, lam = c * s := ⟨_, rfl⟩
  have hlam : lam ∈ Qbar := hlam_def ▸ Qbar.mul_mem hc hs
  have hlam1 : lam * conj lam = 1 := by
    rw [hlam_def, map_mul, hsr]; linear_combination h_c
  have hlam0 : lam ≠ 0 := by rintro h; rw [h] at hlam1; simp at hlam1
  obtain ⟨f, hf_def⟩ : ∃ f : ℂ, f = g' * (s + lam * u) := ⟨_, rfl⟩
  have hfconj : conj f = f := by
    rw [hf_def, map_mul, map_add, map_mul, hg'conj, hsr, hlam_def, map_mul, hsr]
    linear_combination (-(c * conj c * s * g' )) * hss + g' * s * h_c
  have hden : s + lam * u ≠ 0 := by
    intro h
    apply hu
    have : u = -s / lam := by field_simp; linear_combination h
    rw [this]
    exact Qbar.div_mem (Qbar.neg_mem hs) hlam
  have hfg : f / (s + lam * u) = g' := by rw [hf_def]; field_simp
  refine ⟨lam, f, hlam, hlam1, hfconj, ?_⟩
  rw [hfg]
  apply le_antisymm
  · set M := Submodule.span Qbar ({1, u, conj u, f, g'} : Set ℂ)
    have m1 : (1 : ℂ) ∈ M := Submodule.subset_span (by simp)
    have mu : u ∈ M := Submodule.subset_span (by simp)
    have mcu : conj u ∈ M := Submodule.subset_span (by simp)
    have mf : f ∈ M := Submodule.subset_span (by simp)
    have mg' : g' ∈ M := Submodule.subset_span (by simp)
    have hlinv : lam⁻¹ ∈ Qbar := Qbar.inv_mem hlam
    refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨m1, mu, mcu, ?_, ?_⟩
    · have : g = g' + (-q) * conj u := by rw [hg'_def]; ring
      rw [this]
      exact M.add_mem mg' (mul_mem_span (Qbar.neg_mem hq) mcu)
    · have : u * g = lam⁻¹ * f + (-(lam⁻¹ * s)) * g' + (-(q * (s * s))) * 1 := by
        rw [hf_def, hg'_def]; field_simp; linear_combination (q * lam) * hss
      rw [this]
      exact M.add_mem (M.add_mem (mul_mem_span hlinv mf)
        (mul_mem_span (Qbar.neg_mem (Qbar.mul_mem hlinv hs)) mg'))
        (mul_mem_span (Qbar.neg_mem (Qbar.mul_mem hq hss')) m1)
  · set M := Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ)
    have m1 : (1 : ℂ) ∈ M := Submodule.subset_span (by simp)
    have mu : u ∈ M := Submodule.subset_span (by simp)
    have mcu : conj u ∈ M := Submodule.subset_span (by simp)
    have mg : g ∈ M := Submodule.subset_span (by simp)
    have mug : u * g ∈ M := Submodule.subset_span (by simp)
    have mg' : g' ∈ M := hg'_def ▸ M.add_mem mg (mul_mem_span hq mcu)
    refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨m1, mu, mcu, ?_, mg'⟩
    have : f = s * g + (s * q) * conj u + lam * (u * g) + (lam * q * (s * s)) * 1 := by
      rw [hf_def, hg'_def]; linear_combination (-(lam * q)) * hss
    rw [this]
    exact M.add_mem (M.add_mem (M.add_mem (mul_mem_span hs mg)
      (mul_mem_span (Qbar.mul_mem hs hq) mcu)) (mul_mem_span hlam mug))
      (mul_mem_span (Qbar.mul_mem (Qbar.mul_mem hlam hq) hss') m1)
