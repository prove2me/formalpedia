-- Prove2me | solution 1 for FiniteEnergyPlane.crApply_bijective_of_window
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T18:22:23.180202+00:00
-- url     : https://prove2.me/submissions/76327587-17e2-4281-a55d-f52331f3643a

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_of_crApply_eq_zero
import Theorems.Thm_FiniteEnergyPlane_eq_zero_of_crOp_window
import Theorems.Thm_FiniteEnergyPlane_fredholm_index_zero_of_window
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_bijective
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_pi_smul_one



/-!
# Reduction of `crApply_bijective_of_window` to its children

Injectivity: a kernel element has a smooth bounded representative solving the equation classically,
which vanishes under the window; a triple with vanishing first component in the kernel is zero.
Surjectivity: Fredholm of index `0` with trivial kernel.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

lemma crApply_add_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (v w : Triple 1 p) :
    crApply S (v + w) =ᵐ[cylMeasure] crApply S v + crApply S w := by
  filter_upwards [Lp.coeFn_add v.1 w.1, Lp.coeFn_add v.2.1 w.2.1, Lp.coeFn_add v.2.2 w.2.2]
    with x h1 h2 h3
  simp only [crApply, Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h2, h3, map_add]
  abel

lemma crApply_smul_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (r : ℝ) (w : Triple 1 p) :
    crApply S (r • w) =ᵐ[cylMeasure] r • crApply S w := by
  filter_upwards [Lp.coeFn_smul r w.1, Lp.coeFn_smul r w.2.1, Lp.coeFn_smul r w.2.2]
    with x h1 h2 h3
  simp only [crApply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, h1, h2, h3, map_smul,
    smul_add]

lemma crApply_zero_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) :
    crApply S (0 : Triple 1 p) =ᵐ[cylMeasure] 0 := by
  filter_upwards [Lp.coeFn_zero (Vec 1) p cylMeasure] with x h
  simp only [crApply, Prod.fst_zero, Prod.snd_zero, h, Pi.zero_apply, map_zero, add_zero]

/-- Every element of `crRange` is an image. -/
lemma mem_crRange_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (f : LpCyl 1 p)
    (hf : f ∈ crRange p S) :
    ∃ w ∈ W1p p 1, (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply S w := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact hf
  | zero =>
    refine ⟨0, (W1p p 1).zero_mem, ?_⟩
    filter_upwards [Lp.coeFn_zero (Vec 1) p cylMeasure, crApply_zero_ae p S] with x h1 h2
    rw [h1, h2]
  | add f g _ _ hf hg =>
    obtain ⟨v, hv, hfv⟩ := hf
    obtain ⟨w, hw, hgw⟩ := hg
    refine ⟨v + w, (W1p p 1).add_mem hv hw, ?_⟩
    filter_upwards [Lp.coeFn_add f g, hfv, hgw, crApply_add_ae p S v w] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, Pi.add_apply, h2, h3]
  | smul r f _ hf =>
    obtain ⟨v, hv, hfv⟩ := hf
    refine ⟨r • v, (W1p p 1).smul_mem r hv, ?_⟩
    filter_upwards [Lp.coeFn_smul r f, hfv, crApply_smul_ae p S r v] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, Pi.smul_apply, h2]

namespace QL

/-- The weighted coefficient is smooth and periodic. -/
lemma wcoeff_smooth (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => (S x + deriv χ x.1 • (1 : Mat 1)) i j) := by
  intro i j
  have hd : ContDiff ℝ ∞ (deriv χ) := hχ.iterate_deriv 1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact (hS i j).add ((hd.comp contDiff_fst).mul contDiff_const)

/-- A triple whose first component vanishes and which is killed by `D_M` is zero. -/
lemma eq_zero_of_fst_ae_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (M : ℝ × ℝ → Mat 1) (w : Triple 1 p) (hw : w ∈ W1p p 1)
    (h0 : crApply M w =ᵐ[cylMeasure] 0) (h1 : (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0) :
    w = 0 := by
  have hA : crApply (fun x : ℝ × ℝ => (fun _ : ℝ => π • (1 : Mat 1)) x.2) w
      =ᵐ[cylMeasure] 0 := by
    filter_upwards [h0, h1] with x hx hx1
    simp only [crApply, Pi.zero_apply] at hx hx1 ⊢
    rw [hx1, map_zero, add_zero] at hx ⊢
    exact hx
  obtain ⟨hk, -⟩ := translationInvariant_bijective 1 p hp hp' (fun _ : ℝ => π • (1 : Mat 1))
    (isNondegenerate_pi_smul_one 1).1 (isNondegenerate_pi_smul_one 1).2
  have hmem : w ∈ crKernel p (fun x : ℝ × ℝ => (fun _ : ℝ => π • (1 : Mat 1)) x.2) :=
    Submodule.subset_span ⟨hw, hA⟩
  rw [hk] at hmem
  exact (Submodule.mem_bot ℝ).1 hmem

end QL

/-- Glue: the weighted normal operator is bijective. -/
theorem crApply_bijective_of_window_aux (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    (∀ w ∈ W1p p 1, crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 →
        w = 0) ∧
      ∀ f : LpCyl 1 p, ∃ w ∈ W1p p 1,
        (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
          crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w := by
  set M : ℝ × ℝ → Mat 1 := fun x => S x + deriv χ x.1 • (1 : Mat 1) with hMdef
  have hp1 : 1 < p := lt_trans (by norm_num) hp
  have hM := QL.wcoeff_smooth S hS χ hχ.1
  have hMper : ∀ s t : ℝ, M (s, t + 1) = M (s, t) := fun s t => by simp [hMdef, hSper]
  have hinj : ∀ w ∈ W1p p 1, crApply M w =ᵐ[cylMeasure] 0 → w = 0 := by
    intro w hw h0
    obtain ⟨g, hg, hgper, hwg, heq, hgs, hgt⟩ :=
      exists_smooth_of_crApply_eq_zero p hp hp' M hM hMper w hw h0
    obtain ⟨C, hC⟩ := exists_continuous_representative_of_mem_W1p p hp hp' 1
    have hB := ((hC w hw).2 g hg.continuous hgper hwg).1
    have hz := eq_zero_of_crOp_window p hp hp' Sinf hSinf hSinf' δ hδe hwin S hS hSper d hd
      hSas hA χ hχ g hg hgper _ hB heq hgs hgt
    refine QL.eq_zero_of_fst_ae_eq_zero p hp1 hp' M w hw h0 ?_
    filter_upwards [hwg] with x hx
    rw [hx, hz x]; rfl
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨hF, hI⟩ := fredholm_index_zero_of_window p hp1 hp' Sinf hSinf hSinf' δ hδe hwin S hS
    hSper d hd hSas hA χ hχ
  have hk : crKernel p M = ⊥ := (Submodule.span_eq_bot).2 fun w hw => hinj w hw.1 hw.2
  have hI' := hI
  rw [crIndex, hk, finrank_bot] at hI'
  haveI := hF.2.2
  have hq : Module.finrank ℝ (LpCyl 1 p ⧸ crRange p M) = 0 := by
    have : ((Module.finrank ℝ (LpCyl 1 p ⧸ crRange p M) : ℕ) : ℤ) = 0 := by
      push_cast at hI'; linarith
    exact_mod_cast this
  have hsub : Subsingleton (LpCyl 1 p ⧸ crRange p M) := Module.finrank_zero_iff.1 hq
  have hr : crRange p M = ⊤ := Submodule.Quotient.subsingleton_iff.1 hsub
  exact mem_crRange_iff p M f (hr ▸ Submodule.mem_top)

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    (∀ w ∈ W1p p 1, crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 →
        w = 0) ∧
      ∀ f : LpCyl 1 p, ∃ w ∈ W1p p 1,
        (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w :=
  crApply_bijective_of_window_aux p hp hp' Sinf hSinf hSinf' δ hδe hwin S hS hSper d hd hSas hA χ hχ
