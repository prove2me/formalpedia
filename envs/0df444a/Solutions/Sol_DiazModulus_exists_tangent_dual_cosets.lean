-- Prove2me | solution 1 for DiazModulus.exists_tangent_dual_cosets
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:59.85952+00:00
-- url     : https://prove2.me/submissions/7c53a158-5028-4833-ad39-5e6148bc2167

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusDeriv_torusTransl
import Theorems.Thm_DiazModulus_restrictSupport_block_filtration

open Complex ComplexConjugate

/-! # Dual pairs on a finite union of cosets, by Chinese-remainder separators (DALAG Lemma 8.15)

The points `g_s γ` (`|s| ≤ M₁`, `γ ∈ Γ`) lie in the finitely many cosets `c ∈ Cs ⊆ G ⧸ Γ` of the `g_s`; with
`r_c = (c.out)⁻¹` the coset `c` is `{z | z r_c ∈ Γ}`, and `I_c` is its vanishing ideal. For `c ≠ c'` we have
`r_c r_{c'}⁻¹ ∉ Γ`, so `I_c ⊔ I_{c'} = ⊤` by `hcop`. The Chinese-remainder step
(`Ideal.isCoprime_biInf` against `⨅_{c' ≠ c} I_{c'}`) gives `B_c` with `B_c ≡ 1` on the coset `c` and `B_c = 0`
on every other coset of `Cs`. Put `Q_j = Σ_c B_c (B_c · τ_{r_c} P_j)`, where `τ_g f = f ∘ τ_g`
(`eval_torusTransl`). At a point `z` of the coset `c` only the `c`-term survives: it vanishes since
`P_j(z r_c) = 0`, and by Leibniz and `D_w τ_g = τ_g D_w` (node `torusDeriv_torusTransl`) its derivative is
`(D_{w_i} P_j)(z r_c) = δ_ij`. Every polynomial lies in some box (node `restrictSupport_block_filtration`),
and the sum of the boxes of the `Q_j` contains them all. -/

namespace C13_W2
open DiazModulus MvPolynomial

theorem mem_torusVanishing_iff {K A₀ A₁ : Type*} [Field K] {S : Set (TorusGroup K A₀ A₁)}
    {f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K} :
    f ∈ torusVanishing S ↔ ∀ g ∈ S, eval (torusPt g) f = 0 := by
  simp [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]

theorem exists_separator {R ι : Type*} [CommRing R] [DecidableEq ι] (I : ι → Ideal R) (s : Finset ι)
    (hI : ∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → I c ⊔ I c' = ⊤) (c : ι) (hc : c ∈ s) :
    ∃ e : R, 1 - e ∈ I c ∧ ∀ c' ∈ s, c' ≠ c → e ∈ I c' := by
  have h : IsCoprime (I c) (⨅ c' ∈ s.erase c, I c') :=
    Ideal.isCoprime_biInf fun c' hc' => Ideal.isCoprime_iff_sup_eq.2
      (hI c hc c' (Finset.mem_of_mem_erase hc') (Finset.ne_of_mem_erase hc').symm)
  obtain ⟨u, hu, e, he, hue⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨e, by rwa [← hue, add_sub_cancel_right], fun c' hc' hne => ?_⟩
  simp only [Submodule.mem_iInf] at he
  exact he c' (Finset.mem_erase.2 ⟨hne, hc'⟩)

end C13_W2

open DiazModulus C13_W2 MvPolynomial in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁))
    (hcop : ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤)
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₁ n : ℕ) (w : Fin n → (A₀ → ℂ) × (A₁ → ℂ)) (P : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (hP : ∀ j, P j ∈ torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁)))
    (hwP : ∀ i j, torusDeriv (w i) (P j) - (if i = j then 1 else 0) ∈ torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) :
    ∃ (Q : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (CQ : A₀ ⊕ A₁ → ℕ), (∀ j, Q j ∈ torusBox ℂ A₀ A₁ CQ) ∧
      (∀ j, Q j ∈ torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}) ∧
      ∀ i j, torusDeriv (w i) (Q j) - (if i = j then 1 else 0) ∈ torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ} := by
  classical
  let Sb : Finset (B₁ → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M₁ : ℤ)) M₁
  let Cs : Finset (TorusGroup ℂ A₀ A₁ ⧸ Γ) :=
    Sb.image fun s => (hmePoint u a s : TorusGroup ℂ A₀ A₁ ⧸ Γ)
  let r : TorusGroup ℂ A₀ A₁ ⧸ Γ → TorusGroup ℂ A₀ A₁ := fun c => c.out⁻¹
  let I : TorusGroup ℂ A₀ A₁ ⧸ Γ → Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :=
    fun c => torusVanishing {z | z * r c ∈ Γ}
  have hIc : ∀ c ∈ Cs, ∀ c' ∈ Cs, c ≠ c' → I c ⊔ I c' = ⊤ := by
    intro c _ c' _ hne
    refine hcop _ _ fun hmem => hne ?_
    have : (c.out : TorusGroup ℂ A₀ A₁ ⧸ Γ) = (c'.out : TorusGroup ℂ A₀ A₁ ⧸ Γ) := by
      rw [QuotientGroup.eq]; simpa [r] using hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hsep : ∀ c, ∃ e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ,
      c ∈ Cs → (1 - e ∈ I c ∧ ∀ c' ∈ Cs, c' ≠ c → e ∈ I c') := by
    intro c
    by_cases hc : c ∈ Cs
    · obtain ⟨e, he⟩ := exists_separator I Cs hIc c hc
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose B hB using hsep
  have hBone : ∀ c ∈ Cs, ∀ z, z * r c ∈ Γ → eval (torusPt z) (B c) = 1 := by
    intro c hc z hz
    have := mem_torusVanishing_iff.1 (hB c hc).1 z hz
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hBzero : ∀ c ∈ Cs, ∀ c' ∈ Cs, c' ≠ c → ∀ z, z * r c ∈ Γ → eval (torusPt z) (B c') = 0 :=
    fun c hc c' hc' hne z hz => mem_torusVanishing_iff.1 ((hB c' hc').2 c hc hne.symm) z hz
  have hcov : ∀ z ∈ {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ},
      ∃ c ∈ Cs, z * r c ∈ Γ := by
    rintro z ⟨s, hs, γ, hγ, rfl⟩
    refine ⟨(hmePoint u a s : TorusGroup ℂ A₀ A₁ ⧸ Γ), Finset.mem_image.2 ⟨s, ?_, rfl⟩, ?_⟩
    · simp only [Sb, Fintype.mem_piFinset, Finset.mem_Icc]
      exact fun b => abs_le.1 (hs b)
    · have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (hmePoint u a s : TorusGroup ℂ A₀ A₁ ⧸ Γ))
      simp only [r]
      rw [mul_right_comm, mul_comm (hmePoint u a s)]
      exact Γ.mul_mem h1 hγ
  let Q : Fin n → MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ := fun j =>
    ∑ c ∈ Cs, B c * (B c * torusTransl (r c) (P j))
  have hBox := fun j => (DiazModulus.restrictSupport_block_filtration (K := ℂ)
    (Sum.map (id : A₀ → A₀) (Prod.fst : A₁ × Bool → A₁))).2.2 (Q j)
  choose T hT using hBox
  refine ⟨Q, ∑ j, T j, fun j => ?_, fun j => ?_, fun i j => ?_⟩
  · have hTj := hT j
    simp only [torusBox, blockBox] at hTj ⊢
    refine MvPolynomial.restrictSupport_mono ℂ ?_ hTj
    intro m hm b
    refine le_trans (hm b) ?_
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j' => T j' b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · rw [mem_torusVanishing_iff]
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcov z hz
    have hPz : eval (torusPt (z * r c)) (P j) = 0 := mem_torusVanishing_iff.1 (hP j) _ hzc
    simp only [Q, map_sum, map_mul, eval_torusTransl]
    rw [Finset.sum_eq_single_of_mem c hc fun c' hc' hne => by simp [hBzero c hc c' hc' hne z hzc]]
    simp [hPz]
  · rw [mem_torusVanishing_iff]
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcov z hz
    have hPz : eval (torusPt (z * r c)) (P j) = 0 := mem_torusVanishing_iff.1 (hP j) _ hzc
    have hwPz := mem_torusVanishing_iff.1 (hwP i j) _ hzc
    have hδ : ∀ y y' : TorusGroup ℂ A₀ A₁,
        eval (torusPt y) (if i = j then (1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) else 0) =
          eval (torusPt y') (if i = j then (1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) else 0) := by
      intro y y'; split_ifs <;> simp
    have hDQ : eval (torusPt z) (torusDeriv (w i) (Q j)) =
        eval (torusPt (z * r c)) (torusDeriv (w i) (P j)) := by
      simp only [Q, map_sum, Derivation.leibniz, smul_eq_mul, DiazModulus.torusDeriv_torusTransl,
        map_add, map_mul, eval_torusTransl]
      rw [Finset.sum_eq_single_of_mem c hc fun c' hc' hne => by simp [hBzero c hc c' hc' hne z hzc]]
      simp [hPz, hBone c hc z hzc]
    rw [map_sub] at hwPz ⊢
    rw [hDQ, hδ z (z * r c)]
    exact hwPz
