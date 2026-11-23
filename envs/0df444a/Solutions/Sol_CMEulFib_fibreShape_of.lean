-- Prove2me | solution 1 for CMEulFib.fibreShape_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:41.834713+00:00
-- url     : https://prove2.me/submissions/a4f6e872-1535-4e8d-bc31-68e97bc7febe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Theorems.Thm_CMEulFib_mem_map_iff
import Theorems.Thm_CMEulFib_map_map_self
import Theorems.Thm_CMEulFib_comap_map_eq
import Theorems.Thm_CMEulFib_eq_or_eq_map
import Theorems.Thm_CMDeg_finrank_eq_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEulFib
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEulFib
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hFE : IsCMPair F E) (σ : 𝓞 E ≃+* 𝓞 E)
    (hinv : ∀ x : 𝓞 E, σ (σ x) = x)
    (hconj : ∀ P : Ideal (𝓞 E), conjIdeal (K := E) P = P.map σ)
    (hrange : ∀ x : 𝓞 E, σ x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E)))
    (hunr : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ : 𝓞 E, θ - σ θ ∉ P)
    (v : Ideal (𝓞 F)) (hv : v.IsMaximal) : CMEul.FibreShape F E v := by
  classical
  have hfixA : ∀ y : 𝓞 F, σ (algebraMap (𝓞 F) (𝓞 E) y) = algebraMap (𝓞 F) (𝓞 E) y :=
    fun y => (hrange _).mpr ⟨y, rfl⟩
  have hfix : ∀ x : 𝓞 E, σ x = x → x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E)) :=
    fun x hx => (hrange x).mp hx
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact CMDeg.finrank_eq_two hFE
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v
  have hPc : P.comap (algebraMap (𝓞 F) (𝓞 E)) = v := hPv.over.symm
  have : Fintype (v.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v (𝓞 E)
  rw [hdeg] at hsum
  have hmem : ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v →
      Q = P ∨ Q = P.map σ := by
    intro Q hQ hQv
    exact eq_or_eq_map σ hinv hfix P Q (by rw [hQv, hPc])
  have hσPc : (P.map σ).comap (algebraMap (𝓞 F) (𝓞 E)) = v := by
    rw [comap_map_eq σ hinv hfixA, hPc]
  have hσPmax : (P.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ
  have hσPv : (P.map σ).LiesOver v := ⟨hσPc.symm⟩
  have hpos : ∀ q : v.primesOver (𝓞 E),
      1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 (𝓞 F)) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  let p0 : v.primesOver (𝓞 E) := ⟨P, hPmax.isPrime, hPv⟩
  by_cases hfixP : P.map σ = P
  · left
    have hone : ∀ q : v.primesOver (𝓞 E), q = p0 := by
      rintro ⟨q, hq1, hq2⟩
      have := hq1
      have := hq2
      have hqmax : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q v
      apply Subtype.ext
      rcases hmem q hqmax hq2.over.symm with h | h
      · exact h
      · exact h.trans hfixP
    have h2 : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 2 := by
      rw [← hsum, Fintype.sum_eq_single p0 (fun q hq => absurd (hone q) hq)]
    have hf1 : P.inertiaDeg (𝓞 F) ≠ 1 := by
      intro hf
      let : Field (𝓞 F ⧸ v) := Ideal.Quotient.field v
      let : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
      rw [Ideal.inertiaDeg_eq_of_isMaximal v P] at hf
      have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hf
      obtain ⟨θ, hθ⟩ := hunr P hPmax
      obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
      obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at ha
      have hz : θ - algebraMap (𝓞 F) (𝓞 E) a' ∈ P := by
        have := P.neg_mem ha
        simpa using this
      have hz' : σ (θ - algebraMap (𝓞 F) (𝓞 E) a') ∈ P := by
        rw [← mem_map_iff σ hinv, hfixP]
        exact hz
      rw [map_sub, hfixA] at hz'
      apply hθ
      have := P.sub_mem hz hz'
      simpa using this
    have hfpos : 0 < P.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P (𝓞 F)
    have hfle : P.inertiaDeg (𝓞 F) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h2)
    have hf2 : P.inertiaDeg (𝓞 F) = 2 := by omega
    refine ⟨P, hPmax, hPc, by rw [hconj, hfixP], ?_, fun Q hQ hQv => ?_⟩
    · rw [← Ideal.absNorm_pow_inertiaDeg v P, hf2]
    · rcases hmem Q hQ hQv with h | h
      · exact h
      · exact h.trans hfixP
  · right
    let p1 : v.primesOver (𝓞 E) := ⟨P.map σ, hσPmax.isPrime, hσPv⟩
    have hne : p0 ≠ p1 := fun h => hfixP (congrArg Subtype.val h).symm
    have hle : (p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F)) +
        (p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F)) ≤ 2 := by
      rw [← hsum, ← Finset.sum_pair (f := fun q : v.primesOver (𝓞 E) =>
        q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)) hne]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h0 := hpos p0
    have h1 := hpos p1
    have hf0 : p0.1.inertiaDeg (𝓞 F) = 1 := by
      have hm : p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F) = 1 := by omega
      have := Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)
      have := Ideal.inertiaDeg_pos p0.1 (𝓞 F)
      omega
    have hf1 : p1.1.inertiaDeg (𝓞 F) = 1 := by
      have hm : p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F) = 1 := by omega
      have := Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)
      have := Ideal.inertiaDeg_pos p1.1 (𝓞 F)
      omega
    refine ⟨P, P.map σ, hPmax, hσPmax, hPc, hσPc, Ne.symm hfixP, hconj P,
      by rw [hconj, map_map_self σ hinv], ?_, ?_, fun R hR hRv => hmem R hR hRv⟩
    · rw [← Ideal.absNorm_pow_inertiaDeg v P]
      simp only [p0] at hf0
      rw [hf0, pow_one]
    · rw [← Ideal.absNorm_pow_inertiaDeg v (P.map σ)]
      simp only [p1] at hf1
      rw [hf1, pow_one]
end CMEulFib
