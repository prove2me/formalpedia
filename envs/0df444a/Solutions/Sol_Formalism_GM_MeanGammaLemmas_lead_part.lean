-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.lead_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:51.000294+00:00
-- url     : https://prove2.me/submissions/f802057c-de3d-43e5-8d8e-3ff8276d37c0

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_binMatK_eval_nat
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_init_basis
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_det_block_norm
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_sum_trunc
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_entry_deg
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_entry_lead
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_betaT_ne_zero
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_GM_Top_detBlockLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (hDeg : GamDeg) (hLead : GamLead) {p : ℕ} [hp : Fact p.Prime] {K r : ℕ} [NeZero r]
    (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ)
    (w : Fin r → ℤ) (n₀ : ℕ) (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ)
    (κ : ℝ) (m cI : ℕ) (cc : Fin n₀ → Fin n₀ → ℕ → ℤ_[p]) (hr1 : 1 ≤ r) (hv : LLw.vec (Fin.last K) = true)
    (hli : LinearIndependent ℤ_[p] f) (hspan : Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w)
    (hord : ∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e)
    (hL4 : GramDeterminantGradedHypothesis p LLw J M ρ κ)
    (hcc : ∀ x y (n : ℕ), LLw.total ≤ n →
      ((p : ℚ_[p]) ^ cI) * tieGam p LLw ρ z n (f x) (f y) =
        ∑ i ∈ range (LLw.total + LLw.deg (Fin.last K) + 1), (cc x y i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])) :
    (∀ x y (n : ℕ), LLw.total ≤ n →
      ((binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)) x y).eval (n : ℚ_[p]) =
        (p : ℚ_[p]) ^ (m + cI) * tieGam p LLw ρ z n (f x) (f y)) ∧
    (binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.natDegree =
      ∑ b, (LLw.total + LLw.deg (Fin.last K) - ord b) ∧
    ∏ b, (‖betaT p (m + cI) z (LLw.deg (Fin.last K)) LLw.total (ord b)‖ * (p : ℝ) ^ (-κ)) ≤
      ‖(binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.leadingCoeff‖ ∧
    (∀ b, ord b ≤ LLw.deg (Fin.last K)) ∧ LLw.deg (Fin.last K) ≤ LLw.total := by
  classical
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hoS : LLw.deg (Fin.last K) ≤ LLw.total :=
    Finset.single_le_sum (f := LLw.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hord_le : ∀ b, ord b ≤ LLw.deg (Fin.last K) := by
    intro b
    obtain ⟨mm, hm, hme⟩ := (hord b).2
    have hmd : MultiDeg LLw mm := ((MvPolynomial.mem_restrictSupport_iff _).mp (hPol b)) hm
    have := hmd (Fin.last K)
    rw [← this, ← hme]
    exact Finset.single_le_sum (f := fun c => mm (Fin.last K, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) m cc) with hAqdef

  have hAeval : ∀ x y (n : ℕ), S ≤ n → (Aq x y).eval (n : ℚ_[p]) =
      (p : ℚ_[p]) ^ (m + cI) * tieGam p LLw ρ z n (f x) (f y) := by
    intro x y n hn
    rw [hAqdef, binMatK_eval_nat]
    simp only [coefT, ite_mul, zero_mul]
    rw [sum_trunc (S + o) (2 * S) (by omega)]
    simp only [mul_assoc]
    rw [← Finset.mul_sum, ← hcc x y n hn, pow_add, mul_assoc]

  have hAdeg : ∀ x y, (Aq x y).natDegree + max (ord x) (ord y) ≤ S + o := by
    intro x y
    have := entry_deg hDeg LLw ρ z (ord x) (ord y) (f x) (f y) hr1 hv (hPol x) (hPol y) (hord x) (hord y)
      (Aq x y) _ (hAeval x y)
    have h1 := hord_le x; have h2 := hord_le y
    have : max (ord x) (ord y) ≤ o := max_le h1 h2
    omega

  have hAtop : ∀ x y, ord x = ord y → (Aq x y).coeff (S + o - ord x) =
      betaT p (m + cI) z o S (ord x) * gramT p LLw ρ f ord x y := by
    intro x y hxy
    have hy : HasOrder (Fin.last K, ρ) (ord x) (f y) := hxy ▸ hord y
    rw [entry_lead hLead LLw ρ z (ord x) (f x) (f y) hr1 hv (hPol x) (hPol y) (hord x) hy (Aq x y) _
      (pow_ne_zero _ hp0) (hAeval x y)]
    simp only [betaT, gramT, Matrix.of_apply]
    push_cast
    ring
  obtain ⟨hdeg1, hcoef, hlead⟩ := Formalism.GM.Top.detBlockLead ℚ_[p] n₀ Aq (S + o) ord
    (fun i => (hord_le i).trans (by omega)) hAdeg
  set B := Matrix.of fun i j => if ord i = ord j then (Aq i j).coeff (S + o - ord i) else 0 with hBdef
  have hB : ∀ i j, B i j = if ord i = ord j then betaT p (m + cI) z o S (ord i) * gramT p LLw ρ f ord i j
      else 0 := by
    intro i j
    simp only [hBdef, Matrix.of_apply]
    split_ifs with h
    · exact hAtop i j h
    · rfl

  have hstep : ∀ e x, x ∈ FilE p LLw J M ρ w (Fin.last K, ρ) e → initPart (Fin.last K, ρ) e x = 0 →
      x ∈ FilE p LLw J M ρ w (Fin.last K, ρ) (e + 1) := by
    intro e x hx h0
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hx'.1, ?_⟩
    rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    have h2 := hx'.2
    rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h2
    intro mm hmm
    have h3 : e ≤ mm (Fin.last K, ρ) := h2 hmm
    show e + 1 ≤ mm (Fin.last K, ρ)
    rcases Nat.lt_or_eq_of_le h3 with h | h
    · exact h
    · exfalso
      have hc := congrArg (MvPolynomial.coeff mm) h0
      rw [coeff_initPart, if_pos h.symm, MvPolynomial.coeff_zero] at hc
      exact (MvPolynomial.mem_support_iff.mp hmm) hc

  have hGblk : ∀ a', ((p : ℝ) ^ (-κ)) ^ (Fintype.card {b // ord b = a'}) ≤
      ‖((gramT p LLw ρ f ord).toSquareBlock ord a').det‖ := by
    intro a'
    set k := Fintype.card {b // ord b = a'}
    let σe : {b // ord b = a'} ≃ Fin k := Fintype.equivFin _
    let g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
      fun i => initPart (Fin.last K, ρ) a' (f (σe.symm i))
    obtain ⟨hli', hsp'⟩ := init_basis f ord (Fin.last K, ρ) (FilE p LLw J M ρ w (Fin.last K, ρ)) hli hord hfil
      hstep a'
    have hg_li : LinearIndependent ℤ_[p] g := by
      have h0 : LinearIndependent ℤ_[p] (fun b : {b // ord b = a'} => initPart (Fin.last K, ρ) a' (f b)) := hli'
      exact h0.comp σe.symm σe.symm.injective
    have hg_sp : Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) a' := by
      unfold grLat
      rw [← hsp']
      congr 1
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(σe.symm i : Fin n₀), (σe.symm i).2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        refine ⟨σe ⟨b, hb⟩, ?_⟩
        simp [g]
    have h4 := hL4 w a' k g hg_li hg_sp
    have hmat : (Matrix.of fun i j => fock p (g i) (g j) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])) =
        Matrix.reindex σe σe ((gramT p LLw ρ f ord).toSquareBlock ord a') := by
      ext i j
      simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
        gramT, g]
      rw [(σe.symm i).2]
    rw [hmat, Matrix.det_reindex_self] at h4
    have hp0' : (0 : ℝ) ≤ p := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0']
    convert h4 using 2
    ring
  have hBnorm := det_block_norm B (gramT p LLw ρ f ord) ord (betaT p (m + cI) z o S) ((p : ℝ) ^ (-κ))
    (by positivity) hB hGblk
  have hprod_pos : 0 < ∏ b, (‖betaT p (m + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ)) := by
    apply Finset.prod_pos
    intro b _
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos hpr _)
  have hBne : B.det ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hprod_pos hBnorm)
  obtain ⟨hnat, hlc⟩ := hlead hBne
  refine ⟨hAeval, hnat, ?_, hord_le, hoS⟩
  rw [hlc]
  exact hBnorm
end Formalism.GM.MeanGammaLemmas
