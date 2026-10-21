-- Prove2me | solution 1 for CauchyRiemannIndex.index_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T15:48:58.111304+00:00
-- url     : https://prove2.me/submissions/129eefba-32ef-4a5e-a47c-18811a02382a

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_CauchyRiemannIndex_isFredholm
import Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_asymptoticCZIndex_eq
import Theorems.Thm_CauchyRiemannIndex_index_independent_of_p
import Theorems.Thm_CauchyRiemannIndex_exists_asymptotic_crIndex_eq_sub
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_bijective
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_diamond
import Theorems.Thm_CauchyRiemannIndex_crIndex_diamond
import Theorems.Thm_CauchyRiemannIndex_isAsymptoticTo_diamond
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_pi_smul_one



/-!
# The index formula on the cylinder (parent sketch)
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

lemma cif_crIndex_eq_zero_of_bijective {m : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat m)
    (hk : crKernel p S = ⊥) (hr : crRange p S = ⊤) : crIndex p S = 0 := by
  unfold crIndex
  rw [hk, hr, finrank_bot]
  haveI : Subsingleton (LpCyl m p ⧸ (⊤ : Submodule ℝ (LpCyl m p))) := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.eq _).2 Submodule.mem_top⟩
  rw [Module.finrank_zero_of_subsingleton]
  simp

lemma cif_isAsymptoticTo_const {m : ℕ} (L : ℝ → Mat m) (hL : IsSymLoop L) :
    IsAsymptoticTo (fun x : ℝ × ℝ => L x.2) L L := by
  refine ⟨hL.1.comp continuous_snd, fun s t => hL.2.1 t, fun ε hε => ⟨0, fun s t i j => ?_⟩⟩
  simp [hε.le]

/-- Every pair of integers is realised by a reference operator in every positive dimension. -/
lemma cif_reference (m : ℕ) (a b : ℤ) :
    ∃ (T : ℝ × ℝ → Mat (m + 1)) (Tplus Tminus : ℝ → Mat (m + 1)),
      IsSymLoop Tplus ∧ IsSymLoop Tminus ∧ IsNondegenerate Tplus ∧ IsNondegenerate Tminus ∧
        asymptoticCZIndex Tplus = a ∧ asymptoticCZIndex Tminus = b ∧
          IsAsymptoticTo T Tplus Tminus ∧ crIndex 2 T = a - b := by
  obtain ⟨hLs, hLn⟩ := isNondegenerate_pi_smul_one m
  set L : ℝ → Mat m := fun _ => Real.pi • (1 : Mat m)
  set c := asymptoticCZIndex L
  obtain ⟨T₁, Mp, Mm, hMp, hMm, hnMp, hnMm, hμp, hμm, hT₁, hind₁⟩ :=
    exists_asymptotic_crIndex_eq_sub (a - c) (b - c)
  have hT₀ := cif_isAsymptoticTo_const L hLs
  obtain ⟨hk₀, hr₀⟩ := translationInvariant_bijective m 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top L hLs hLn
  have hind₀ : crIndex 2 (fun x : ℝ × ℝ => L x.2) = 0 := cif_crIndex_eq_zero_of_bijective 2 _ hk₀ hr₀
  obtain ⟨hDps, hDpn, hDpμ⟩ := asymptoticCZIndex_diamond L Mp hLs hMp hLn hnMp
  obtain ⟨hDms, hDmn, hDmμ⟩ := asymptoticCZIndex_diamond L Mm hLs hMm hLn hnMm
  have hF₀ := isFredholm m 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top L L hLs hLs _ hT₀ hLn hLn
  have hF₁ := isFredholm 1 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Mp Mm hMp hMm T₁ hT₁ hnMp hnMm
  refine ⟨fun x => ConleyZehnder.diamond (L x.2) (T₁ x),
    fun t => ConleyZehnder.diamond (L t) (Mp t), fun t => ConleyZehnder.diamond (L t) (Mm t),
    hDps, hDms, hDpn, hDmn, ?_, ?_, isAsymptoticTo_diamond _ _ _ _ _ _ hT₀ hT₁, ?_⟩
  · rw [hDpμ, hμp]; ring
  · rw [hDmμ, hμm]; ring
  · rw [crIndex_diamond 2 _ _ hF₀ hF₁, hind₀, hind₁]; ring

lemma cif_dim_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (Splus Sminus : ℝ → Mat 0) (S : ℝ × ℝ → Mat 0) :
    crIndex p S = asymptoticCZIndex Splus - asymptoticCZIndex Sminus := by
  have hS : Splus = Sminus := funext fun t => Subsingleton.elim _ _
  haveI : Subsingleton (Vec 0) := inferInstance
  haveI : Subsingleton (LpCyl 0 p) :=
    ⟨fun f g => Lp.ext (Filter.Eventually.of_forall fun x => Subsingleton.elim _ _)⟩
  haveI : Subsingleton (crKernel p S) := inferInstance
  unfold crIndex
  rw [Module.finrank_zero_of_subsingleton (M := crKernel p S),
    Module.finrank_zero_of_subsingleton (M := LpCyl 0 p ⧸ crRange p S), hS]
  simp

theorem index_formula_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus) :
    IsFredholmCR p S ∧ crIndex p S = asymptoticCZIndex Splus - asymptoticCZIndex Sminus := by
  refine ⟨isFredholm n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus, ?_⟩
  cases n with
  | zero => exact cif_dim_zero p Splus Sminus S
  | succ m =>
    obtain ⟨T, Tp, Tm, hTp, hTm, hnTp, hnTm, hμp, hμm, hT, hind⟩ :=
      cif_reference m (asymptoticCZIndex Splus) (asymptoticCZIndex Sminus)
    rw [crIndex_eq_of_asymptoticCZIndex_eq (m + 1) p hp hp' Splus Sminus Tp Tm hSplus hSminus
      hTp hTm hplus hminus hnTp hnTm hμp.symm hμm.symm S T hS hT]
    rw [(index_independent_of_p (m + 1) p hp hp' Tp Tm hTp hTm T hT hnTp hnTm 2 ENNReal.one_lt_two
      ENNReal.ofNat_ne_top).2, hind]

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    IsFredholmCR p S ∧ crIndex p S = asymptoticCZIndex Splus - asymptoticCZIndex Sminus :=
  CauchyRiemannIndex.index_formula_aux n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus
