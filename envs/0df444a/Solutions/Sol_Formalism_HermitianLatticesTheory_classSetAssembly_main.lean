-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:49.808623+00:00
-- url     : https://prove2.me/submissions/7ab39d34-e122-4375-8af2-fe840e24bb9d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_dint
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_finite_rat
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_le_Q
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_finite_between
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_exists_isom
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_w_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hE : FinIntermediate) (hF : IsomOfTrace)
    (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hdM : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (B : ℝ)
    (hgood : ∀ M ∈ S, ∃ u : Fin n → V, (∀ i, u i ∈ M) ∧ LinearIndependent ℝ (ι ∘ u) ∧
      ∀ i, ‖ι (u i)‖ ≤ B) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ M ∈ s, M ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  classical
  unfold IsomOfTrace at hF
  choose! u humem huli hubd using hgood
  have hωmem : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∀ k x, x ∈ M →
      NumberField.integralBasis K k • x ∈ M := by
    intro M k x hx
    obtain ⟨r, hr⟩ := classSetAssembly_w_mem (K := K) (some k)
    have hr' : NumberField.integralBasis K k = algebraMap (NumberField.RingOfIntegers K) K r := hr
    rw [hr', algebraMap_smul]
    exact M.smul_mem r hx
  obtain ⟨C, hC⟩ : ∃ C : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → ℝ,
      ∀ k x, ‖ι (NumberField.integralBasis K k • x)‖ ≤ C k * ‖ι x‖ :=
    ⟨fun k => (hmul (NumberField.integralBasis K k)).choose,
      fun k => (hmul (NumberField.integralBasis K k)).choose_spec⟩
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, B * B ≤ R ∧ ∀ k, |C k| * B * B ≤ R := by
    have hs : 0 ≤ ∑ k, |C k| := Finset.sum_nonneg fun k _ => abs_nonneg (C k)
    refine ⟨B * B * (1 + ∑ k, |C k|), ?_, fun k => ?_⟩
    · exact le_mul_of_one_le_right (mul_self_nonneg B) (by linarith)
    · have hk : |C k| ≤ 1 + ∑ k, |C k| := by
        have := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ k)
        linarith
      calc |C k| * B * B = B * B * |C k| := by ring
        _ ≤ B * B * (1 + ∑ k, |C k|) := mul_le_mul_of_nonneg_left hk (mul_self_nonneg B)
  have hT := classSetAssembly_finite_rat d hd R
  have hbound : ∀ M ∈ S, ∀ x y : V, x ∈ M → y ∈ M → ∀ c : ℝ, ‖ι x‖ ≤ c → ‖ι y‖ ≤ B →
      c * B ≤ R → Algebra.trace ℚ K (h x y) ∈
        {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R} := by
    intro M hM x y hx hy c hc hyB hcR
    refine ⟨classSetAssembly_dint h d x y (hdM M hM x hx y hy), ?_⟩
    rw [← hι]
    calc |inner ℝ (ι x) (ι y)| ≤ ‖ι x‖ * ‖ι y‖ := abs_real_inner_le_norm _ _
      _ ≤ c * B := mul_le_mul hc hyB (norm_nonneg _) ((norm_nonneg _).trans hc)
      _ ≤ R := hcR
  obtain ⟨D, hD⟩ : ∃ D : Submodule (NumberField.RingOfIntegers K) V →
      (Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ),
      ∀ M, D M = (fun i l => Algebra.trace ℚ K (h (u M i) (u M l)),
        fun k i l => Algebra.trace ℚ K (h (NumberField.integralBasis K k • u M i) (u M l))) :=
    ⟨_, fun _ => rfl⟩
  have hDfin : (D '' S).Finite := by
    refine ((Set.Finite.pi fun i => Set.Finite.pi fun l => hT).prod
      (Set.Finite.pi fun k => Set.Finite.pi fun i => Set.Finite.pi fun l => hT)).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [hD]
    refine Set.mem_prod.mpr ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_,
      Set.mem_univ_pi.mpr fun k => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_⟩
    · exact hbound M hM _ _ (humem M hM i) (humem M hM l) B (hubd M hM i) (hubd M hM l) hR1
    · refine hbound M hM _ _ (hωmem M k _ (humem M hM i)) (humem M hM l) (|C k| * B) ?_
        (hubd M hM l) (hR2 k)
      exact (hC k _).trans (mul_le_mul (le_abs_self _) (hubd M hM i) (norm_nonneg _) (abs_nonneg _))
  have hEprop : ∀ M ∈ S, ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V,
      (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u M j)) = z) →
      x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u M i) := by
    intro M hM
    obtain ⟨e, he, hx⟩ := classSetAssembly_denom h hpos ι hι (u M) (huli M hM) d hd
      (fun i j => classSetAssembly_dint h d (u M i) (u M j)
        (hdM M hM _ (humem M hM i) _ (humem M hM j)))
    exact ⟨e, he, fun x hxj => classSetAssembly_le_Q (K := K) (u M) e he x (hx x hxj)⟩
  choose! e he hemem using hEprop
  have hφex : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∃ φ : V ≃ₗ[K] V, M ∈ S →
      (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u (Function.invFunOn D S (D M)) i) = u M i := by
    intro M
    by_cases hM : M ∈ S
    · obtain ⟨hRS, hRD⟩ : Function.invFunOn D S (D M) ∈ S ∧
          D (Function.invFunOn D S (D M)) = D M := Function.invFunOn_pos ⟨M, hM, rfl⟩
      generalize Function.invFunOn D S (D M) = M₀ at hRS hRD ⊢
      have h1 := congrArg Prod.fst hRD
      have h2 := congrArg Prod.snd hRD
      rw [hD M₀, hD M] at h1 h2
      obtain ⟨φ, h3, h4⟩ := classSetAssembly_exists_isom h hpos ι hι
        (NumberField.integralBasis K) (u M₀) (u M) (huli M₀ hRS) (huli M hM)
        (fun i l => congrFun (congrFun h1 i) l)
        (fun k i l => congrFun (congrFun (congrFun h2 k) i) l)
      exact ⟨φ, fun _ => ⟨h3, h4⟩⟩
    · exact ⟨LinearEquiv.refl K V, fun h' => absurd h' hM⟩
  choose φ hφ using hφex
  obtain ⟨Key, hKey⟩ : ∃ Key : Submodule (NumberField.RingOfIntegers K) V →
      ((Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ)) ×
        AddSubgroup V,
      ∀ M, Key M = (D M, M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom) :=
    ⟨_, fun _ => rfl⟩
  have hKfin : (Key '' S).Finite := by
    refine (Set.Finite.biUnion hDfin fun δ hδ =>
      ((classSetAssembly_finite_between (K := K) hE (u (Function.invFunOn D S δ))
        (e (Function.invFunOn D S δ)) (he _ (Function.invFunOn_pos hδ).1)).image
          (Prod.mk δ))).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [Set.mem_iUnion₂]
    refine ⟨D M, ⟨M, hM, rfl⟩, ?_⟩
    rw [hKey]
    have hRS : Function.invFunOn D S (D M) ∈ S := (Function.invFunOn_pos ⟨M, hM, rfl⟩).1
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show φ M (u (Function.invFunOn D S (D M)) i) ∈ M
      rw [(hφ M hM).2 i]
      exact humem M hM i
    · intro x hx
      have hx' : φ M x ∈ M := hx
      refine hemem _ hRS x (fun j => ?_)
      rw [← (hφ M hM).1 x, (hφ M hM).2 j]
      exact classSetAssembly_dint h d _ _ (hdM M hM _ hx' _ (humem M hM j))
  refine ⟨hKfin.toFinset.image (Function.invFunOn Key S), ?_, ?_⟩
  · intro N hN
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hN
    exact (Function.invFunOn_pos (hKfin.mem_toFinset.mp hy)).1
  · intro M hM
    have hy : Key M ∈ Key '' S := ⟨M, hM, rfl⟩
    obtain ⟨hNS, hNK⟩ := Function.invFunOn_pos hy
    refine ⟨Function.invFunOn Key S (Key M),
      Finset.mem_image.mpr ⟨Key M, hKfin.mem_toFinset.mpr hy, rfl⟩, ?_⟩
    generalize Function.invFunOn Key S (Key M) = N at hNS hNK ⊢
    rw [hKey N, hKey M] at hNK
    have hCN : N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom =
        M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := congrArg Prod.snd hNK
    refine ⟨(φ N).symm.trans (φ M), ?_, ?_⟩
    · apply hF K V h
      intro x y
      show Algebra.trace ℚ K (h (φ M ((φ N).symm x)) (φ M ((φ N).symm y))) =
        Algebra.trace ℚ K (h x y)
      rw [(hφ M hM).1]
      have h5 := (hφ N hNS).1 ((φ N).symm x) ((φ N).symm y)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h5
      exact h5.symm
    · ext x
      rw [isomAct_mem_gmap]
      have hc : (φ M).symm x ∈ N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom ↔
          (φ M).symm x ∈ M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := by
        rw [hCN]
      change φ N ((φ M).symm x) ∈ N ↔ φ M ((φ M).symm x) ∈ M at hc
      rw [LinearEquiv.apply_symm_apply] at hc
      exact hc
end Formalism.HermitianLatticesTheory
