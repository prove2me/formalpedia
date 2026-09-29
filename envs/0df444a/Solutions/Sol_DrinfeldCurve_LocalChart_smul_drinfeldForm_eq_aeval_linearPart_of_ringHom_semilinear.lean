-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/860af59c-9679-5cef-89a0-c37f13cc3365

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear

set_option autoImplicit false

namespace FormTransportAux

open MvPowerSeries

variable {W : Type} [CommRing W]

local notation "IX" => (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} : Ideal (MvPowerSeries (Fin 2) W))

theorem degree_fin_two (n : Fin 2 →₀ ℕ) : n.degree = n 0 + n 1 := by
  have h : ∑ i ∈ n.support, n i = ∑ i, n i :=
    Finset.sum_subset (Finset.subset_univ _) (by intro i _ hi; simpa using hi)
  show ∑ i ∈ n.support, n i = n 0 + n 1
  rw [h, Fin.sum_univ_two]

theorem mem_IX_pow_iff (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    g ∈ IX ^ e ↔ ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → coeff n g = 0 :=
  MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g

theorem pow_sub_pow_mem {R : Type} [CommRing R] (P : Ideal R) (a b : R) (ha : a ∈ P) (hb : b ∈ P)
    (hab : a - b ∈ P ^ 2) (k : ℕ) : a ^ k - b ^ k ∈ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
    rw [this]
    refine add_mem ?_ ?_
    · rw [show k + 1 + 1 = 1 + (k + 1) by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul ha ih
    · rw [show k + 1 + 1 = 2 + k by ring, pow_add]
      exact Ideal.mul_mem_mul hab (Ideal.pow_mem_pow hb k)

theorem coeff_mul_of_mem_pow (k : ℕ) (a b : MvPowerSeries (Fin 2) W) (ha : a ∈ IX ^ k)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 = k) :
    coeff n (a * b) = coeff n a * constantCoeff b := by
  classical
  rw [coeff_mul]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hij' : i + j = n := hij
    by_cases hi : i = n
    · exfalso; apply hne
      subst hi
      have : j = 0 := by
        have := congrArg (fun x => x - i) hij'; simpa using this
      simp [this]
    · have hlt : i 0 + i 1 < k := by
        have h0 : i 0 ≤ n 0 := by rw [← hij']; simp
        have h1 : i 1 ≤ n 1 := by rw [← hij']; simp
        rcases Nat.lt_or_ge (i 0 + i 1) k with h | h
        · exact h
        · exfalso; apply hi; ext x; fin_cases x <;> simp <;> omega
      rw [(mem_IX_pow_iff k a).mp ha i hlt, zero_mul]
  · simp

end FormTransportAux

namespace FormTransportAux

open MvPowerSeries

variable {W : Type} [CommRing W]
local notation "IX" => (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} : Ideal (MvPowerSeries (Fin 2) W))

theorem X_mem_IX (i : Fin 2) : (X i : MvPowerSeries (Fin 2) W) ∈ IX := by
  fin_cases i
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)

theorem sub_trunc_mem (N : ℕ) (p : MvPowerSeries (Fin 2) W) :
    p - ((MvPowerSeries.truncTotal N p : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) ∈ IX ^ N := by
  rw [mem_IX_pow_iff]
  intro n hn
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ (by rw [degree_fin_two]; exact hn), sub_self]

theorem linear_mem_IX (c : Fin 2 → W) : (∑ ii : Fin 2, C (c ii) * X ii : MvPowerSeries (Fin 2) W) ∈ IX :=
  Ideal.sum_mem _ (fun ii _ => Ideal.mul_mem_left _ _ (X_mem_IX ii))

end FormTransportAux

open MvPowerSeries FormTransportAux in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] (t : W) (ht : t ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}) →+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (σ : W →+* W) (hσ : ∀ w : W, σ w - w ∈ Ideal.span {t}) (w₁ : W) (hw₁ : σ t = t * w₁)
    (hθC : ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.C w)) =
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.C (σ w)))
    (M : Matrix (Fin 2) (Fin 2) W)
    (hM : ∀ jj : Fin 2, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
          (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)}) ^ 2) :
    Ideal.Quotient.mk (Ideal.span {t}) w₁ •
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) =
      MvPolynomial.aeval
        (fun jj : Fin 2 => ∑ ii : Fin 2,
          MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {t}) (M ii jj)) * MvPolynomial.X ii)
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) := by
  classical

  have hJ : Ideal.span {Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (X 0 : MvPowerSeries (Fin 2) W),
      Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (X 1)} =
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) := by
    rw [Ideal.map_span]; congr 1; ext x; simp [Set.image_insert_eq]
  have hlift : ∀ jj : Fin 2, ∃ h : MvPowerSeries (Fin 2) W,
      h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2 ∧
      θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (X jj)) =
        Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) ((∑ ii : Fin 2, C (M ii jj) * X ii) + h) := by
    intro jj
    have := hM jj
    rw [hJ, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
    obtain ⟨h, hh, hθh⟩ := this
    refine ⟨h, hh, ?_⟩
    rw [map_add, hθh]; ring
  choose h hh hθh using hlift

  obtain ⟨I, hI⟩ : ∃ I : Ideal (MvPowerSeries (Fin 2) W), I = Ideal.span {C t * v - f * u} := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin 2 → MvPowerSeries (Fin 2) W, L = fun jj => ∑ ii : Fin 2, C (M ii jj) * X ii := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → MvPowerSeries (Fin 2) W, g = fun jj => L jj + h jj := ⟨_, rfl⟩
  have hgIX : ∀ jj, g jj ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := by
    intro jj; rw [hg, hL]; exact add_mem (linear_mem_IX _) (Ideal.pow_le_self two_ne_zero (hh jj))
  have hgL : ∀ jj, g jj - L jj ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2 := by
    intro jj; rw [hg]; simpa using hh jj
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MvPolynomial (Fin 2) W →+* MvPowerSeries (Fin 2) W,
      Θ = MvPolynomial.eval₂Hom ((C : W →+* MvPowerSeries (Fin 2) W).comp σ) g := ⟨_, rfl⟩
  have hΘC : ∀ w : W, Θ (MvPolynomial.C w) = C (σ w) := by intro w; rw [hΘ]; simp
  have hΘX : ∀ jj : Fin 2, Θ (MvPolynomial.X jj) = g jj := by intro jj; rw [hΘ]; simp

  have hcomp : θ.comp ((Ideal.Quotient.mk (Ideal.span {C t * v - f * u})).comp
      (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin 2) W →+* MvPowerSeries (Fin 2) W)) =
      (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})).comp Θ := by
    apply MvPolynomial.ringHom_ext
    · intro w
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_C, hΘC, hθC]
    · intro jj
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_X, hΘX, hθh, hg, hL]
  have hΘmk : ∀ p : MvPolynomial (Fin 2) W,
      θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (p : MvPowerSeries (Fin 2) W)) =
        Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ p) := fun p => RingHom.congr_fun hcomp p

  have hJle : Ideal.map θ (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}))
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ≤
      Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap, Ideal.span_le]
    intro x hx
    simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply]
    have hgIX' : ∀ jj, (∑ ii : Fin 2, C (M ii jj) * X ii) + h jj ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := by
      intro jj; simpa [hg, hL] using hgIX jj
    rcases hx with rfl | hx
    · rw [hθh 0]; exact Ideal.mem_map_of_mem _ (hgIX' 0)
    · rw [Set.mem_singleton_iff] at hx; subst hx
      rw [hθh 1]; exact Ideal.mem_map_of_mem _ (hgIX' 1)
  have hθJ : ∀ (N : ℕ) (x : MvPowerSeries (Fin 2) W ⧸ Ideal.span {C t * v - f * u}),
      x ∈ (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ^ N →
      θ x ∈ (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ^ N := by
    intro N x hx
    have := Ideal.mem_map_of_mem θ hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hJle N this

  have happrox : ∀ (N : ℕ) (p : MvPowerSeries (Fin 2) W),
      θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) p) -
        Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ (MvPowerSeries.truncTotal N p)) ∈
      (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ^ N := by
    intro N p
    have h1 := sub_trunc_mem N p
    have h2 : Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (p - (MvPowerSeries.truncTotal N p : MvPolynomial (Fin 2) W)) ∈
        (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ^ N := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h1
    have h3 := hθJ N _ h2
    rw [map_sub, map_sub, hΘmk] at h3
    exact h3

  have hrel : Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C t) * Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v =
      Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) f * Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact Ideal.subset_span (by simp)
  have hid : Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (f * u * C w₁) * θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v) =
      θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) f) * θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u) *
        Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v := by
    have e1 : θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C t)) =
        Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C t) * Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C w₁) := by
      rw [hθC, hw₁, map_mul, map_mul]
    calc Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (f * u * C w₁) * θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v)
        = (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) f * Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u) *
            Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C w₁) * θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v) := by
          rw [map_mul, map_mul]
      _ = θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C t) * Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v) *
            Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v := by
          rw [← hrel, map_mul, e1]; ring
      _ = θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) f) * θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u) *
            Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v := by
          rw [hrel, map_mul]

  obtain ⟨G, hGdef⟩ : ∃ G : MvPowerSeries (Fin 2) W,
      G = f * u * C w₁ * Θ (MvPowerSeries.truncTotal (q + 2) v) -
        Θ (MvPowerSeries.truncTotal (q + 2) f) * Θ (MvPowerSeries.truncTotal (q + 2) u) * v := ⟨_, rfl⟩
  have hrv := happrox (q + 2) v
  have hrf := happrox (q + 2) f
  have hru := happrox (q + 2) u
  have hGJ : Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) G ∈
      (Ideal.map (Ideal.Quotient.mk (Ideal.span {C t * v - f * u})) (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})) ^ (q + 2) := by
    have key : Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) G =
        -(Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (f * u * C w₁) *
            (θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v) -
              Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ (MvPowerSeries.truncTotal (q + 2) v)))) +
          ((θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) f) -
              Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ (MvPowerSeries.truncTotal (q + 2) f))) *
              θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u) +
            Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ (MvPowerSeries.truncTotal (q + 2) f)) *
              (θ (Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) u) -
                Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (Θ (MvPowerSeries.truncTotal (q + 2) u)))) *
            Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) v := by
      have hid' := hid
      simp only [map_mul] at hid'
      simp only [hGdef, map_sub, map_mul]
      linear_combination hid'
    rw [key]
    refine add_mem (neg_mem_iff.mpr (Ideal.mul_mem_left _ _ hrv)) (Ideal.mul_mem_right _ _ (add_mem ?_ ?_))
    · exact Ideal.mul_mem_right _ _ hrf
    · exact Ideal.mul_mem_left _ _ hru

  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hGJ
  obtain ⟨y, hy, hyG⟩ := hGJ
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hyG
  obtain ⟨r, hr⟩ := hyG
  have hGyr : G = y + (C t * v - f * u) * (-r) := by linear_combination hr

  obtain ⟨Fp, hFp⟩ : ∃ Fp : MvPolynomial (Fin 2) W,
      Fp = MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 := ⟨_, rfl⟩
  obtain ⟨Lp, hLp⟩ : ∃ Lp : Fin 2 → MvPolynomial (Fin 2) W,
      Lp = fun jj => ∑ ii : Fin 2, MvPolynomial.C (M ii jj) * MvPolynomial.X ii := ⟨_, rfl⟩
  obtain ⟨Λp, hΛp⟩ : ∃ Λp : MvPolynomial (Fin 2) W, Λp = Lp 0 * Lp 1 ^ q - Lp 0 ^ q * Lp 1 := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hFhom : Fp.IsHomogeneous (q + 1) := by
    rw [hFp]
    refine MvPolynomial.IsHomogeneous.sub ?_ ?_
    · have := (MvPolynomial.isHomogeneous_X W (0 : Fin 2)).mul ((MvPolynomial.isHomogeneous_X W (1 : Fin 2)).pow q)
      simpa [add_comm] using this
    · have := ((MvPolynomial.isHomogeneous_X W (0 : Fin 2)).pow q).mul (MvPolynomial.isHomogeneous_X W (1 : Fin 2))
      simpa using this
  have hLhom : ∀ jj, (Lp jj).IsHomogeneous 1 := by
    intro jj; rw [hLp]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun ii _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  have hΛhom : Λp.IsHomogeneous (q + 1) := by
    rw [hΛp]
    refine MvPolynomial.IsHomogeneous.sub ?_ ?_
    · have := (hLhom 0).mul ((hLhom 1).pow q)
      simpa [add_comm] using this
    · have := ((hLhom 0).pow q).mul (hLhom 1)
      simpa using this
  have hFcoe : (Fp : MvPowerSeries (Fin 2) W) = DrinfeldCurve.LocalChart.drinfeldForm q W := by
    rw [hFp]; unfold DrinfeldCurve.LocalChart.drinfeldForm
    change MvPolynomial.coeToMvPowerSeries.ringHom
      (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 : MvPolynomial (Fin 2) W) = _
    simp only [map_sub, map_mul, map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
  have hLcoe : ∀ jj, (Lp jj : MvPowerSeries (Fin 2) W) = L jj := by
    intro jj; rw [hLp, hL]
    change MvPolynomial.coeToMvPowerSeries.ringHom (∑ ii : Fin 2, MvPolynomial.C (M ii jj) * MvPolynomial.X ii) = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ii _ => ?_)
    rw [map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_C, MvPolynomial.coe_X]
  have hΛcoe : (Λp : MvPowerSeries (Fin 2) W) = L 0 * L 1 ^ q - L 0 ^ q * L 1 := by
    rw [hΛp]
    change MvPolynomial.coeToMvPowerSeries.ringHom (Lp 0 * Lp 1 ^ q - Lp 0 ^ q * Lp 1) = _
    simp only [map_sub, map_mul, map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, hLcoe]

  have hfN : MvPowerSeries.truncTotal (q + 2) f = Fp := by
    ext n
    by_cases hn : n.degree < q + 2
    · rw [MvPowerSeries.coeff_truncTotal _ hn]
      have h0 := (mem_IX_pow_iff (q + 2) _).mp hf n (by rw [← degree_fin_two]; exact hn)
      rw [map_sub, sub_eq_zero, ← hFcoe, MvPolynomial.coeff_coe] at h0
      exact h0
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp hn)]
      exact (hFhom.coeff_eq_zero (by omega)).symm
  have hΘF : Θ Fp = g 0 * g 1 ^ q - g 0 ^ q * g 1 := by
    rw [hFp]; simp only [map_sub, map_mul, map_pow, hΘX]

  have hIX1 : Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} = Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ 1 :=
    (pow_one _).symm
  have hLIX : ∀ jj, L jj ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := by
    intro jj; rw [hL]; exact linear_mem_IX _
  have hprod1 : ∀ (a b : MvPowerSeries (Fin 2) W), a ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} →
      b ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} →
      a * b ^ q ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    intro a b ha hb
    rw [show q + 1 = 1 + q by ring, pow_add, pow_one]
    exact Ideal.mul_mem_mul ha (Ideal.pow_mem_pow hb q)
  have hprod2 : ∀ (a b : MvPowerSeries (Fin 2) W), a ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} →
      b ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} →
      a ^ q * b ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    intro a b ha hb
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ha q) hb
  have hΘFmem : Θ Fp ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    rw [hΘF]; exact sub_mem (hprod1 _ _ (hgIX 0) (hgIX 1)) (hprod2 _ _ (hgIX 0) (hgIX 1))
  have hFmem : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    unfold DrinfeldCurve.LocalChart.drinfeldForm
    exact sub_mem (hprod1 _ _ (X_mem_IX 0) (X_mem_IX 1)) (hprod2 _ _ (X_mem_IX 0) (X_mem_IX 1))
  have hfmem : f ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    have : f = (f - DrinfeldCurve.LocalChart.drinfeldForm q W) + DrinfeldCurve.LocalChart.drinfeldForm q W := by ring
    rw [this]; exact add_mem (Ideal.pow_le_pow_right (by omega) hf) hFmem
  have hΘFΛ : Θ Fp - (L 0 * L 1 ^ q - L 0 ^ q * L 1) ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 2) := by
    rw [hΘF]
    have e : g 0 * g 1 ^ q - g 0 ^ q * g 1 - (L 0 * L 1 ^ q - L 0 ^ q * L 1) =
        ((g 0 - L 0) * g 1 ^ q + L 0 * (g 1 ^ q - L 1 ^ q)) - ((g 0 ^ q - L 0 ^ q) * g 1 + L 0 ^ q * (g 1 - L 1)) := by ring
    rw [e]
    refine sub_mem (add_mem ?_ ?_) (add_mem ?_ ?_)
    · rw [show q + 2 = 2 + q by ring, pow_add]; exact Ideal.mul_mem_mul (hgL 0) (Ideal.pow_mem_pow (hgIX 1) q)
    · rw [show q + 2 = 1 + (q + 1) by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul (hLIX 0) (pow_sub_pow_mem _ _ _ (hgIX 1) (hLIX 1) (hgL 1) q)
    · rw [show q + 2 = (q + 1) + 1 by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul (pow_sub_pow_mem _ _ _ (hgIX 0) (hLIX 0) (hgL 0) q) (hgIX 1)
    · rw [show q + 2 = q + 2 by rfl, pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hLIX 0) q) (hgL 1)

  have hGmem : G ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ (q + 1) := by
    rw [hGdef, hfN]
    refine sub_mem ?_ ?_
    · rw [mul_assoc, mul_assoc]; exact Ideal.mul_mem_right _ _ hfmem
    · rw [mul_assoc]; exact Ideal.mul_mem_right _ _ hΘFmem
  have hGlow := (mem_IX_pow_iff (q + 1) G).mp hGmem
  have hylow := (mem_IX_pow_iff (q + 2) y).mp hy
  have hf0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0 := (mem_IX_pow_iff (q + 1) f).mp hfmem 0 (by simp)
  have hcoefG : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 = q + 1 → MvPowerSeries.coeff n G ∈ Ideal.span {t} :=
    fun n hn => DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero W t ht f u v hv hf0
      (q + 1) G y (-r) hGlow hylow hGyr n hn

  have hg0 : ∀ jj, MvPowerSeries.constantCoeff (g jj) = 0 := fun jj =>
    (mem_IX_pow_iff 1 _).mp (by simpa using hgIX jj) 0 (by simp)
  have hΘ0 : ∀ p : MvPolynomial (Fin 2) W, MvPowerSeries.constantCoeff (Θ p) = σ (MvPolynomial.constantCoeff p) := by
    intro p
    have hc : (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W →+* W).comp Θ = σ.comp MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro w
        simp only [RingHom.coe_comp, Function.comp_apply, hΘC, MvPowerSeries.constantCoeff_C, MvPolynomial.constantCoeff_C]
      · intro jj
        simp only [RingHom.coe_comp, Function.comp_apply, hΘX, hg0, MvPolynomial.constantCoeff_X, map_zero]
    exact RingHom.congr_fun hc p
  have hcv : MvPolynomial.constantCoeff (MvPowerSeries.truncTotal (q + 2) v) = MvPowerSeries.constantCoeff v := by
    show MvPolynomial.coeff 0 (MvPowerSeries.truncTotal (q + 2) v) = MvPowerSeries.coeff 0 v
    exact MvPowerSeries.coeff_truncTotal _ (by simp)
  have hcu : MvPolynomial.constantCoeff (MvPowerSeries.truncTotal (q + 2) u) = MvPowerSeries.constantCoeff u := by
    show MvPolynomial.coeff 0 (MvPowerSeries.truncTotal (q + 2) u) = MvPowerSeries.coeff 0 u
    exact MvPowerSeries.coeff_truncTotal _ (by simp)
  have hu0 : IsUnit (MvPowerSeries.constantCoeff u) := hu.map _
  have hv0 : IsUnit (MvPowerSeries.constantCoeff v) := hv.map _

  have hcoefG' : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 = q + 1 →
      MvPowerSeries.coeff n G =
        MvPowerSeries.coeff n f * (MvPowerSeries.constantCoeff u * w₁ * σ (MvPowerSeries.constantCoeff v)) -
        MvPowerSeries.coeff n (L 0 * L 1 ^ q - L 0 ^ q * L 1) * (σ (MvPowerSeries.constantCoeff u) * MvPowerSeries.constantCoeff v) := by
    intro n hn
    have e1 : MvPowerSeries.coeff n (f * u * C w₁ * Θ (MvPowerSeries.truncTotal (q + 2) v)) =
        MvPowerSeries.coeff n f * (MvPowerSeries.constantCoeff u * w₁ * σ (MvPowerSeries.constantCoeff v)) := by
      rw [mul_assoc, mul_assoc, coeff_mul_of_mem_pow (q + 1) f _ hfmem n hn, map_mul, map_mul,
        MvPowerSeries.constantCoeff_C, hΘ0, hcv, mul_assoc]
    have e2 : MvPowerSeries.coeff n (Θ (MvPowerSeries.truncTotal (q + 2) f) * Θ (MvPowerSeries.truncTotal (q + 2) u) * v) =
        MvPowerSeries.coeff n (L 0 * L 1 ^ q - L 0 ^ q * L 1) * (σ (MvPowerSeries.constantCoeff u) * MvPowerSeries.constantCoeff v) := by
      rw [hfN, mul_assoc, coeff_mul_of_mem_pow (q + 1) _ _ hΘFmem n hn, map_mul, hΘ0, hcu]
      congr 1
      have := (mem_IX_pow_iff (q + 2) _).mp hΘFΛ n (by omega)
      rwa [map_sub, sub_eq_zero] at this
    rw [hGdef, map_sub, e1, e2]

  have hmain : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 = q + 1 →
      w₁ * MvPolynomial.coeff n Fp - MvPolynomial.coeff n Λp ∈ Ideal.span {t} := by
    intro n hn
    have hG := hcoefG n hn
    rw [hcoefG' n hn] at hG
    have hfF : MvPowerSeries.coeff n f = MvPolynomial.coeff n Fp := by
      have := (mem_IX_pow_iff (q + 2) _).mp hf n (by omega)
      rw [map_sub, sub_eq_zero, ← hFcoe, MvPolynomial.coeff_coe] at this
      exact this
    have hΛc : MvPowerSeries.coeff n (L 0 * L 1 ^ q - L 0 ^ q * L 1) = MvPolynomial.coeff n Λp := by
      rw [← hΛcoe, MvPolynomial.coeff_coe]
    rw [hfF, hΛc] at hG
    have hsv := hσ (MvPowerSeries.constantCoeff v)
    have hsu := hσ (MvPowerSeries.constantCoeff u)
    have key : MvPowerSeries.constantCoeff u * MvPowerSeries.constantCoeff v *
        (w₁ * MvPolynomial.coeff n Fp - MvPolynomial.coeff n Λp) =
        (MvPolynomial.coeff n Fp * (MvPowerSeries.constantCoeff u * w₁ * σ (MvPowerSeries.constantCoeff v)) -
          MvPolynomial.coeff n Λp * (σ (MvPowerSeries.constantCoeff u) * MvPowerSeries.constantCoeff v)) -
        MvPolynomial.coeff n Fp * MvPowerSeries.constantCoeff u * w₁ *
          (σ (MvPowerSeries.constantCoeff v) - MvPowerSeries.constantCoeff v) +
        MvPolynomial.coeff n Λp * MvPowerSeries.constantCoeff v *
          (σ (MvPowerSeries.constantCoeff u) - MvPowerSeries.constantCoeff u) := by ring
    have hmem : MvPowerSeries.constantCoeff u * MvPowerSeries.constantCoeff v *
        (w₁ * MvPolynomial.coeff n Fp - MvPolynomial.coeff n Λp) ∈ Ideal.span {t} := by
      rw [key]
      exact add_mem (sub_mem hG (Ideal.mul_mem_left _ _ hsv)) (Ideal.mul_mem_left _ _ hsu)
    exact (Ideal.unit_mul_mem_iff_mem _ (hu0.mul hv0)).mp hmem

  have hκF : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) = MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {t})) Fp := by
    rw [hFp]; simp only [map_sub, map_mul, map_pow, MvPolynomial.map_X]
  have hκΛ : MvPolynomial.aeval
        (fun jj : Fin 2 => ∑ ii : Fin 2,
          MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {t}) (M ii jj)) * MvPolynomial.X ii)
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) =
      MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {t})) Λp := by
    rw [hΛp, hLp]
    simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [hκΛ, hκF]
  ext n
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, smul_eq_mul, ← map_mul,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  by_cases hn : n 0 + n 1 = q + 1
  · exact hmain n hn
  · have hd : n.degree ≠ q + 1 := by rw [degree_fin_two]; exact hn
    rw [hFhom.coeff_eq_zero hd, hΛhom.coeff_eq_zero hd, mul_zero, sub_zero]
    exact zero_mem _

end S_DrinfeldCurve_LocalChart_smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear (solution)
