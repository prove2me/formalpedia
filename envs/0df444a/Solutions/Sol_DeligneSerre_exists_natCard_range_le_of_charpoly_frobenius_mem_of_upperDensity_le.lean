-- Prove2me | solution 1 for DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cb9a01df-25a8-5b1f-861b-8c7c100150c7

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation
import Theorems.Thm_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe"

set_option autoImplicit false

open Filter Topology
open scoped MatrixGroups

namespace DeligneSerre84

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem finite_range_of_factorsThroughFiniteLevel {M : Type} [Group M] (ρ : Γℚ →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite (MonoidHom.range ρ) := by
  classical
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  let F : Γℚ → (L →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => σ.toAlgHom.comp L.val
  have hF : ∀ σ τ : Γℚ, F σ = F τ → ρ σ = ρ τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hx' := congrArg (fun φ : L →ₐ[ℚ] AlgebraicClosure ℚ => φ ⟨x, hx⟩) h
      simp only [F, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom] at hx'
      change σ x = τ x at hx'
      rw [AlgEquiv.mul_apply, hx']
      exact τ.symm_apply_apply x
    have h1 : ρ (τ⁻¹ * σ) = 1 := hker _ hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  let g : (L →ₐ[ℚ] AlgebraicClosure ℚ) → M := fun v =>
    if h : ∃ σ : Γℚ, F σ = v then ρ h.choose else 1
  have hsub : (MonoidHom.range ρ : Set M) ⊆ Set.range g := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨F σ, ?_⟩
    have h : ∃ σ' : Γℚ, F σ' = F σ := ⟨σ, rfl⟩
    simp only [g, dif_pos h]
    exact hF _ _ h.choose_spec
  exact Set.Finite.subset (Set.finite_range g) hsub |>.to_subtype

noncomputable def subrepEquiv {k : Type} [Field k] (ρ : Γℚ →* GL (Fin 2) k) :
    Subrepresentation (Deformation.matrixRepresentation ρ) ≃o
      Subrepresentation (Deformation.matrixRepresentation (MonoidHom.range ρ).subtype) where
  toFun W :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        rintro ⟨g, σ, rfl⟩ v hv
        have := W.apply_mem_toSubmodule σ hv
        simpa [Deformation.matrixRepresentation_apply] using this }
  invFun W' :=
    { toSubmodule := W'.toSubmodule
      apply_mem_toSubmodule := by
        intro σ v hv
        have := W'.apply_mem_toSubmodule ⟨ρ σ, σ, rfl⟩ hv
        simpa [Deformation.matrixRepresentation_apply] using this }
  left_inv W := Subrepresentation.toSubmodule_injective rfl
  right_inv W' := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

theorem isSemisimpleRepresentation_range {k : Type} [Field k] (ρ : Γℚ →* GL (Fin 2) k)
    (h : (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation) :
    (Deformation.matrixRepresentation (MonoidHom.range ρ).subtype).IsSemisimpleRepresentation := by
  haveI : ComplementedLattice (Subrepresentation (Deformation.matrixRepresentation ρ)) := h
  exact (subrepEquiv ρ).complementedLattice

theorem tendsto_log_one_div_sub_one :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_sub_right (1 : ℝ)).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hs))
  have h2 : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h3 := Real.tendsto_log_atTop.comp (h2.comp h1)
  refine h3.congr fun s => ?_
  simp [one_div]

theorem summable_rpow_neg {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem rpow_neg_nonneg (s : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem rpow_neg_le_one {s : ℝ} (hs : 0 < s) (n : ℕ) : (n : ℝ) ^ (-s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    exact zero_le_one
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

theorem tsum_subtype_le_of_subset_union {T X' : Set ℕ} {S : Finset ℕ} {s : ℝ} (hs : 1 < s)
    (hT : T ⊆ X' ∪ ↑S) :
    ∑' p : T, ((p : ℕ) : ℝ) ^ (-s) ≤ (∑' p : X', ((p : ℕ) : ℝ) ^ (-s)) + S.card := by
  classical
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ (-s) with hf
  have hf0 : ∀ n, 0 ≤ f n := rpow_neg_nonneg s
  have hsum : Summable f := summable_rpow_neg hs
  rw [tsum_subtype T f, tsum_subtype X' f]
  have hle : ∀ n, T.indicator f n ≤ X'.indicator f n + (↑S : Set ℕ).indicator f n := by
    intro n
    by_cases hn : n ∈ T
    · rw [Set.indicator_of_mem hn]
      rcases hT hn with h | h
      · rw [Set.indicator_of_mem h]
        exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => hf0 _) _)
      · rw [Set.indicator_of_mem h]
        exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ => hf0 _) _)
    · rw [Set.indicator_of_notMem hn]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => hf0 _) _)
        (Set.indicator_nonneg (fun _ _ => hf0 _) _)
  have hS : ∑' n, (↑S : Set ℕ).indicator f n = ∑ n ∈ S, f n := by
    rw [tsum_eq_sum (s := S)]
    · exact Finset.sum_congr rfl fun n hn => Set.indicator_of_mem (Finset.mem_coe.mpr hn) f
    · intro n hn
      exact Set.indicator_of_notMem (fun h => hn (Finset.mem_coe.mp h)) f
  calc ∑' n, T.indicator f n
      ≤ ∑' n, (X'.indicator f n + (↑S : Set ℕ).indicator f n) :=
        (hsum.indicator T).tsum_le_tsum hle ((hsum.indicator X').add (hsum.indicator _))
    _ = (∑' n, X'.indicator f n) + ∑' n, (↑S : Set ℕ).indicator f n :=
        (hsum.indicator X').tsum_add (hsum.indicator _)
    _ ≤ (∑' n, X'.indicator f n) + S.card := by
        rw [hS]
        gcongr
        calc ∑ n ∈ S, f n ≤ ∑ _n ∈ S, (1 : ℝ) :=
              Finset.sum_le_sum fun n _ => rpow_neg_le_one (by linarith) n
          _ = S.card := by simp

theorem le_of_density {c η : ℝ} {T X' : Set ℕ} {S : Finset ℕ} (hT : T ⊆ X' ∪ ↑S)
    (hlow : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (c - δ) * Real.log (1 / (s - 1)) ≤ ∑' p : T, ((p : ℕ) : ℝ) ^ (-s))
    (hX : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ∑' p : X', ((p : ℕ) : ℝ) ^ (-s) ≤ (η + δ) * Real.log (1 / (s - 1))) :
    c ≤ η := by

  have key : ∀ δ : ℝ, 0 < δ → c ≤ η + 2 * δ := by
    intro δ hδ
    obtain ⟨s₁, hs₁, h₁⟩ := hlow δ hδ
    obtain ⟨s₂, hs₂, h₂⟩ := hX δ hδ
    by_contra hlt
    push Not at hlt
    set gap : ℝ := c - η - 2 * δ with hgap
    have hgap0 : 0 < gap := by rw [hgap]; linarith

    have hev₁ : ∀ᶠ s in 𝓝[>] (1 : ℝ), gap * Real.log (1 / (s - 1)) ≤ S.card := by
      have hmem : Set.Ioo (1 : ℝ) (min s₁ s₂) ∈ 𝓝[>] (1 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min hs₁ hs₂)
      filter_upwards [hmem] with s hs
      obtain ⟨hs1, hs12⟩ := hs
      have hA := h₁ s hs1 (hs12.trans_le (min_le_left _ _))
      have hB := h₂ s hs1 (hs12.trans_le (min_le_right _ _))
      have hC := tsum_subtype_le_of_subset_union hs1 hT
      have : (c - δ) * Real.log (1 / (s - 1)) ≤ (η + δ) * Real.log (1 / (s - 1)) + S.card :=
        hA.trans (hC.trans (by linarith))
      rw [hgap]
      linarith

    have hev₂ : ∀ᶠ s in 𝓝[>] (1 : ℝ), (S.card : ℝ) + 1 ≤ gap * Real.log (1 / (s - 1)) :=
      (tendsto_log_one_div_sub_one.const_mul_atTop hgap0).eventually_ge_atTop _
    obtain ⟨s, hle, hge⟩ := (hev₁.and hev₂).exists
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := key (ε / 2) (by linarith)
  linarith

end DeligneSerre84

open DeligneSerre84 in

theorem solution
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) (X : Set ℕ)
    (hX : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
        (η + δ) * Real.log (1 / (s - 1))) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod ℓ)),
      GaloisFactorsThroughFiniteLevel ρ →
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation →
      ∀ (S : Finset ℕ) (P : Finset (Polynomial (ZMod ℓ))), P.card ≤ M →
        (∀ p : ℕ, p.Prime → p ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p → p ∉ X →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly ∈ P) →
        Nat.card (MonoidHom.range ρ) ≤ A := by
  classical
  obtain ⟨A, hA⟩ :=
    Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
      η hη M
  refine ⟨A, ?_⟩
  intro ℓ _ ρ hfl hss S P hPM hdata

  set Q : Subgroup (GL (Fin 2) (ZMod ℓ)) := MonoidHom.range ρ with hQ
  haveI : Finite Q := finite_range_of_factorsThroughFiniteLevel ρ hfl
  letI : Fintype Q := Fintype.ofFinite Q
  let π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Q := ρ.rangeRestrict
  have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective ρ
  have hπρ : ∀ σ, ((π σ : Q) : GL (Fin 2) (ZMod ℓ)) = ρ σ := fun σ => rfl
  have hπfl : GaloisFactorsThroughFiniteLevel π := by
    obtain ⟨L, hL, hker⟩ := hfl
    exact ⟨L, hL, fun σ hσ => Subtype.ext (by rw [hπρ, hker σ hσ]; rfl)⟩

  let good : Q → Prop := fun g =>
    ((g : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly ∈ P
  let Hq : Finset Q := Finset.univ.filter good
  let Cq : Finset Q := Finset.univ.filter fun g => ¬ good g
  let H : Finset (GL (Fin 2) (ZMod ℓ)) := Hq.image Subtype.val
  let C : Set Q := ↑Cq
  have hHcard : H.card = Hq.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hHC : Hq.card + Cq.card = Nat.card Q := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_filter_add_card_filter_not good
  have hCcard : Nat.card C = Cq.card := Nat.card_eq_finsetCard Cq

  have hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C := by
    intro g h hg
    simp only [C, Cq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, good] at hg ⊢
    intro hmem
    apply hg
    have : (((h * g * h⁻¹ : Q) : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) =
        (h : GL (Fin 2) (ZMod ℓ)).val * (g : GL (Fin 2) (ZMod ℓ)).val *
          ((h : GL (Fin 2) (ZMod ℓ)).val)⁻¹ := by
      rw [← Matrix.coe_units_inv]
      simp [Units.val_mul]
    rw [this, Matrix.charpoly_units_conj] at hmem
    exact hmem

  set T : Set ℕ := {p : ℕ | p.Prime ∧
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
        ∃ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p ∧ π σ ∈ C}
    with hT
  set X' : Set ℕ := {p : ℕ | p.Prime ∧ p ∈ X} with hX'
  have hTsub : T ⊆ X' ∪ ↑S := by
    rintro p ⟨hp, -, A, hA, σ, hσ, hσC⟩
    by_cases hpS : p ∈ S
    · exact Or.inr (Finset.mem_coe.mpr hpS)
    · left
      refine ⟨hp, ?_⟩
      by_contra hpX
      have hgood : good (π σ) := (hdata p hp hpS A hA).2 σ hσ hpX
      simp only [C, Cq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσC
      exact hσC hgood

  have hlow : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : T, ((p : ℕ) : ℝ) ^ (-s) := fun δ hδ =>
    GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective π hπs hπfl C hC δ hδ
  have hdens : (Nat.card C : ℝ) / Nat.card Q ≤ η := le_of_density hTsub hlow hX

  have hQpos : (0 : ℝ) < Nat.card Q := by
    have : 0 < Nat.card Q := Nat.card_pos
    exact_mod_cast this
  have hCle : (Cq.card : ℝ) ≤ η * Nat.card Q := by
    rw [← hCcard]
    rwa [div_le_iff₀ hQpos] at hdens
  have hHge : (1 - η) * (Nat.card Q : ℝ) ≤ H.card := by
    rw [hHcard]
    have : (Hq.card : ℝ) + Cq.card = Nat.card Q := by exact_mod_cast hHC
    linarith
  have hHsub : (↑H : Set (GL (Fin 2) (ZMod ℓ))) ⊆ Q := by
    intro g hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hg)
    exact g'.2
  have hHimg : (H.image fun h : GL (Fin 2) (ZMod ℓ) =>
      (h : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly).card ≤ M := by
    refine (Finset.card_le_card ?_).trans hPM
    intro q hq
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hg
    exact (Finset.mem_filter.mp hg').2

  have hssQ := isSemisimpleRepresentation_range ρ hss
  exact hA ℓ Q hssQ H hHsub hHge hHimg

end S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
end P2MW
export P2MW.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le (solution)
