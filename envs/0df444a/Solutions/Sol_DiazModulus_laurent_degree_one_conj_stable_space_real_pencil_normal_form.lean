-- Prove2me | solution 1 for DiazModulus.laurent_degree_one_conj_stable_space_real_pencil_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:32.392859+00:00
-- url     : https://prove2.me/submissions/b7431b9b-892f-42a4-8161-88a2cb7cd12e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_twisted_symmetric_normal_form

open Complex ComplexConjugate

/-! # A conjugation-stable degree-one Laurent space is a real pencil space

Let `v ∉ Q̄` with `v v̄ = 1`, `g = F(v)/v^N`, with `1, v, v̄, g, vg` free over `Q̄` and
`ḡ = a + b v + c·vg` (`a, b, c ∈ Q̄`). Conjugating once more and using `v v̄ = 1` gives
`(ā + c̄ b) + (b̄ + c̄ a) v̄ + (c c̄ − 1) g = 0`, so by the freeness of `1, v̄, g` we get
`c c̄ = 1` and `a = −c b̄`. Then `g' = g − b̄ v̄ = (X F − b̄ X^N)(v)/v^(N+1)` satisfies
`ḡ' = c v g'`, and the twisted symmetric normal form (`laurent_conj_twisted_symmetric_normal_form`)
gives `G` with `G(0) = 0` and `g' ≡ g'' := G(v) + κ conj(v G(v))` modulo `span(1, v̄)`, `κ = c̄`.
The identity `v g'' = κ ḡ''` then shows that `1, v, v̄, g, vg` and `1, v, v̄, g'', ḡ''` span the same
space, each generator being an explicit `Q̄`-combination of the other family. If `deg G ≤ 1`, then
`G = a₁X`: `a₁ = 0` makes `g ∈ span(1, v̄)`, against freeness, and `a₁ ≠ 0` gives
`ḡ'' = ā₁ v̄ + c a₁ v²`, so `v² ∈ W`. -/

namespace R18_M1

open DiazModulus Polynomial

theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

theorem mul_mem_span {S : Set ℂ} {c w : ℂ} (hc : c ∈ Qbar) (hw : w ∈ Submodule.span Qbar S) :
    c * w ∈ Submodule.span Qbar S :=
  Submodule.smul_mem _ (⟨c, hc⟩ : Qbar) hw

/-- `1, v̄, g` are free over `Q̄`. -/
theorem indep3 {v g : ℂ} (hind : LinearIndependent (↥Qbar) ![1, v, conj v, g, v * g])
    {α β γ : ℂ} (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hγ : γ ∈ Qbar)
    (h : α + β * conj v + γ * g = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  have := Fintype.linearIndependent_iff.1 hind
    ![⟨α, hα⟩, 0, ⟨β, hβ⟩, ⟨γ, hγ⟩, 0] (by
      simp [Fin.sum_univ_five, Subfield.smul_def]
      linear_combination h)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val (this 0)
  · simpa using congrArg Subtype.val (this 2)
  · simpa using congrArg Subtype.val (this 3)

end R18_M1

open DiazModulus R18_M1 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (N : ℕ) (F : Polynomial ↥Qbar)
    (hind : LinearIndependent (↥Qbar) ![1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)])
    (hcg : conj (Polynomial.aeval v F / v ^ N) ∈ Submodule.span Qbar ({1, v, v * (Polynomial.aeval v F / v ^ N)} : Set ℂ)) :
    ∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧
      (2 ≤ G.natDegree ∨ v ^ 2 ∈ Submodule.span Qbar ({1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)} : Set ℂ)) ∧
      Submodule.span Qbar ({1, v, conj v, (Polynomial.aeval v F / v ^ N), v * (Polynomial.aeval v F / v ^ N)} : Set ℂ) =
        Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ) := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Qbar.zero_mem)
  have hcv : conj v = v⁻¹ := eq_inv_of_mul_eq_one_right hv1
  set g := Polynomial.aeval v F / v ^ N with hg_def
  obtain ⟨a', b', c', habc⟩ := Submodule.mem_span_triple.1 hcg
  have hcg' : conj g = (a' : ℂ) + (b' : ℂ) * v + (c' : ℂ) * (v * g) := by
    rw [← habc]; simp [Subfield.smul_def]
  have ha : (a' : ℂ) ∈ Qbar := a'.2
  have hb : (b' : ℂ) ∈ Qbar := b'.2
  have hc : (c' : ℂ) ∈ Qbar := c'.2
  generalize (a' : ℂ) = a at hcg' ha
  generalize (b' : ℂ) = b at hcg' hb
  generalize (c' : ℂ) = c at hcg' hc
  have h2 : g = conj a + conj b * conj v + conj c * (conj v * conj g) := by
    have := congrArg conj hcg'
    rw [Complex.conj_conj, map_add, map_add, map_mul, map_mul, map_mul] at this
    exact this
  rw [hcg'] at h2
  obtain ⟨h_a, h_b, h_c⟩ := indep3 hind
    (Qbar.add_mem (conj_mem ha) (Qbar.mul_mem (conj_mem hc) hb))
    (Qbar.add_mem (conj_mem hb) (Qbar.mul_mem (conj_mem hc) ha))
    (Qbar.sub_mem (Qbar.mul_mem hc (conj_mem hc)) Qbar.one_mem)
    (show (conj a + conj c * b) + (conj b + conj c * a) * conj v + (c * conj c - 1) * g = 0 by
      linear_combination (-1 : ℂ) * h2 - (conj c * b + conj c * c * g) * hv1)
  have hcc : c * conj c = 1 := by linear_combination h_c
  have hac : a = -(c * conj b) := by linear_combination c * h_b - a * h_c
  -- the shifted polynomial for `g' = g - b̄ v̄`
  have hbQ : conj b ∈ Qbar := conj_mem hb
  set F' : (↥Qbar)[X] := X * F - C (⟨conj b, hbQ⟩ : ↥Qbar) * X ^ N with hF'_def
  have hg' : aeval v F' / v ^ (N + 1) = g - conj b * conj v := by
    rw [hF'_def, hg_def, hcv]
    simp only [map_sub, map_mul, aeval_X, aeval_C, aeval_X_pow]
    simp only [show algebraMap (↥Qbar) ℂ ⟨conj b, hbQ⟩ = conj b from rfl]
    field_simp
    ring
  have hF : conj (aeval v F' / v ^ (N + 1)) = c * v * (aeval v F' / v ^ (N + 1)) := by
    rw [hg', map_sub, map_mul, Complex.conj_conj, Complex.conj_conj, hcg', hac]
    linear_combination (c * conj b) * hv1
  obtain ⟨G, hG0, hGmem⟩ :=
    DiazModulus.laurent_conj_twisted_symmetric_normal_form v hv hv1 (N + 1) F' c hc hcc hF
  rw [hg'] at hGmem
  set P := aeval v G with hP_def
  set κ := conj c with hκ_def
  have hκ : κ ∈ Qbar := conj_mem hc
  have hκ1 : κ * conj κ = 1 := by rw [hκ_def, Complex.conj_conj]; linear_combination hcc
  set g'' := P + κ * conj (v * P) with hg''_def
  obtain ⟨p', q', hpq⟩ := Submodule.mem_span_pair.1 hGmem
  have hpq' : g - conj b * conj v - g'' = (p' : ℂ) * 1 + (q' : ℂ) * conj v := by
    rw [← hpq]; simp [Subfield.smul_def]
  have hp : (p' : ℂ) ∈ Qbar := p'.2
  have hq : (q' : ℂ) ∈ Qbar := q'.2
  generalize (p' : ℂ) = p at hpq' hp
  generalize (q' : ℂ) = q at hpq' hq
  -- the key identity `v g'' = κ ḡ''`
  have hkey : conj g'' = c * (v * g'') := by
    simp only [hg''_def, hκ_def, map_add, map_mul, Complex.conj_conj]
    linear_combination (-(c * conj c * conj P)) * hv1 - (conj P) * hcc
  have hκc : c * κ = 1 := hcc
  have heq : Submodule.span Qbar ({1, v, conj v, g, v * g} : Set ℂ) =
      Submodule.span Qbar ({1, v, conj v, g'', conj g''} : Set ℂ) := by
    apply le_antisymm
    · set M := Submodule.span Qbar ({1, v, conj v, g'', conj g''} : Set ℂ)
      have m1 : (1 : ℂ) ∈ M := Submodule.subset_span (by simp)
      have mv : v ∈ M := Submodule.subset_span (by simp)
      have mcv : conj v ∈ M := Submodule.subset_span (by simp)
      have mg : g'' ∈ M := Submodule.subset_span (by simp)
      have mcg : conj g'' ∈ M := Submodule.subset_span (by simp)
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨m1, mv, mcv, ?_, ?_⟩
      · have : g = g'' + p * 1 + (q + conj b) * conj v := by linear_combination hpq'
        rw [this]
        exact M.add_mem (M.add_mem mg (mul_mem_span hp m1))
          (mul_mem_span (Qbar.add_mem hq hbQ) mcv)
      · have : v * g = κ * conj g'' + p * v + (q + conj b) * 1 := by
          rw [hkey]
          linear_combination v * hpq' + (q + conj b) * hv1 - (v * g'') * hκc
        rw [this]
        exact M.add_mem (M.add_mem (mul_mem_span hκ mcg) (mul_mem_span hp mv))
          (mul_mem_span (Qbar.add_mem hq hbQ) m1)
    · set M := Submodule.span Qbar ({1, v, conj v, g, v * g} : Set ℂ)
      have m1 : (1 : ℂ) ∈ M := Submodule.subset_span (by simp)
      have mv : v ∈ M := Submodule.subset_span (by simp)
      have mcv : conj v ∈ M := Submodule.subset_span (by simp)
      have mg : g ∈ M := Submodule.subset_span (by simp)
      have mvg : v * g ∈ M := Submodule.subset_span (by simp)
      have mg'' : g'' ∈ M := by
        have : g'' = g + (-p) * 1 + (-(q + conj b)) * conj v := by linear_combination -hpq'
        rw [this]
        exact M.add_mem (M.add_mem mg (mul_mem_span (Qbar.neg_mem hp) m1))
          (mul_mem_span (Qbar.neg_mem (Qbar.add_mem hq hbQ)) mcv)
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨m1, mv, mcv, mg'', ?_⟩
      have : conj g'' = c * (v * g) + (-(c * p)) * v + (-(c * (q + conj b))) * 1 := by
        rw [hkey]
        linear_combination (-(c * v)) * hpq' - (c * (q + conj b)) * hv1
      rw [this]
      exact M.add_mem (M.add_mem (mul_mem_span hc mvg)
        (mul_mem_span (Qbar.neg_mem (Qbar.mul_mem hc hp)) mv))
        (mul_mem_span (Qbar.neg_mem (Qbar.mul_mem hc (Qbar.add_mem hq hbQ))) m1)
  refine ⟨κ, hκ, hκ1, G, hG0, ?_, heq⟩
  by_cases hdeg : 2 ≤ G.natDegree
  · exact Or.inl hdeg
  right
  have hG1 : G = C (G.coeff 1) * X := by
    have := eq_X_add_C_of_natDegree_le_one (show G.natDegree ≤ 1 by omega)
    rw [hG0, map_zero, add_zero] at this
    exact this
  have hPv : P = (G.coeff 1 : ℂ) * v := by
    rw [hP_def]; conv_lhs => rw [hG1]
    rw [map_mul, aeval_C, aeval_X]; rfl
  have ha1 : ((G.coeff 1 : ↥Qbar) : ℂ) ∈ Qbar := (G.coeff 1).2
  generalize ((G.coeff 1 : ↥Qbar) : ℂ) = a1 at hPv ha1
  rw [heq]
  by_cases ha10 : a1 = 0
  · exfalso
    have hg0 : g'' = 0 := by rw [hg''_def, hPv, ha10]; simp
    have := indep3 hind (Qbar.neg_mem hp) (Qbar.neg_mem (Qbar.add_mem hq hbQ))
      Qbar.one_mem (show -p + -(q + conj b) * conj v + 1 * g = 0 by
        linear_combination hpq' + hg0)
    exact one_ne_zero this.2.2
  · have hc0 : c ≠ 0 := by rintro rfl; simp at hcc
    have hcg'' : conj g'' = conj a1 * conj v + c * a1 * v ^ 2 := by
      rw [hkey, hg''_def, hPv]
      simp only [map_mul, hκ_def]
      linear_combination (c * conj c * conj a1 * conj v) * hv1 + (conj a1 * conj v) * hcc
    set M := Submodule.span Qbar ({1, v, conj v, g'', conj g''} : Set ℂ)
    have mcv : conj v ∈ M := Submodule.subset_span (by simp)
    have mcg : conj g'' ∈ M := Submodule.subset_span (by simp)
    have hinv : (c * a1)⁻¹ ∈ Qbar := Qbar.inv_mem (Qbar.mul_mem hc ha1)
    have : v ^ 2 = (c * a1)⁻¹ * conj g'' + (-((c * a1)⁻¹ * conj a1)) * conj v := by
      rw [hcg'']; field_simp; ring
    rw [this]
    exact M.add_mem (mul_mem_span hinv mcg)
      (mul_mem_span (Qbar.neg_mem (Qbar.mul_mem hinv (conj_mem ha1))) mcv)
