-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f410e98c-7df7-5a1a-9103-80b3ad55d239

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span

set_option autoImplicit false

namespace LinPartTransport

noncomputable section

open MvPowerSeries

variable {W : Type} [CommRing W]

abbrev XX (W : Type) [CommRing W] : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}

theorem eq_of_deg_lt_two (n : Fin 2 →₀ ℕ) (h : n 0 + n 1 < 2) :
    n = 0 ∨ n = Finsupp.single 0 1 ∨ n = Finsupp.single 1 1 := by
  rcases Nat.lt_or_ge (n 0) 1 with h0 | h0
  · rcases Nat.lt_or_ge (n 1) 1 with h1 | h1
    · left; ext i; fin_cases i <;> simp <;> omega
    · right; right; ext i; fin_cases i <;> simp <;> omega
  · right; left; ext i; fin_cases i <;> simp <;> omega

theorem coeff_lin (a b : W) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1 :
      MvPowerSeries (Fin 2) W) =
      (if n = Finsupp.single 0 1 then a else 0) + (if n = Finsupp.single 1 1 then b else 0) := by
  classical
  simp only [map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem single_zero_ne_single_one : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
  simp at this

theorem zero_ne_single (i : Fin 2) : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
  intro h
  have := congrArg (fun f : Fin 2 →₀ ℕ => f i) h
  simp at this

theorem sub_lin_mem_sq (φ : MvPowerSeries (Fin 2) W) (hφ : φ ∈ XX W) :
    φ - (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single 0 1) φ) * MvPowerSeries.X 0 +
      MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single 1 1) φ) * MvPowerSeries.X 1) ∈ XX W ^ 2 := by
  classical
  have h0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) φ = 0 := by
    have := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 1 φ).mp (by simpa using hφ)
    exact this 0 (by simp)
  rw [MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt]
  intro n hn
  rcases eq_of_deg_lt_two n hn with rfl | rfl | rfl
  · rw [map_sub, coeff_lin]; simp [h0, zero_ne_single]
  · rw [map_sub, coeff_lin]; simp [single_zero_ne_single_one]
  · rw [map_sub, coeff_lin]; simp [single_zero_ne_single_one.symm]

theorem f_mem_sq (q : ℕ) [Fact q.Prime] (f : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ XX W ^ (q + 2)) : f ∈ XX W ^ 2 := by
  have hq : 1 ≤ q := (Fact.out : q.Prime).one_le
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∈ XX W := Ideal.subset_span (by simp)
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∈ XX W := Ideal.subset_span (by simp)
  have hdf : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ XX W ^ 2 := by
    show MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ q - MvPowerSeries.X 0 ^ q * MvPowerSeries.X 1 ∈ XX W ^ 2
    have hp1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ^ q = MvPowerSeries.X 1 * MvPowerSeries.X 1 ^ (q - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hq]
    have hp0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ^ q = MvPowerSeries.X 0 ^ (q - 1) * MvPowerSeries.X 0 := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [pow_two, hp1, hp0, ← mul_assoc, mul_assoc (MvPowerSeries.X 0 ^ (q - 1))]
    refine Ideal.sub_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX0 hX1)
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX0 hX1)
  have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ XX W ^ 2 := Ideal.pow_le_pow_right (by omega) hf
  have := Ideal.add_mem _ h1 hdf
  simpa using this

section Chart

variable (g : MvPowerSeries (Fin 2) W)

abbrev JJ : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) :=
  Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.X 0), Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.X 1)}

theorem JJ_eq_map : JJ g = (XX W).map (Ideal.Quotient.mk (Ideal.span {g})) := by
  rw [XX, Ideal.map_span, Set.image_pair]

theorem JJ_sq_eq_map : JJ g ^ 2 = (XX W ^ 2).map (Ideal.Quotient.mk (Ideal.span {g})) := by
  rw [Ideal.map_pow, JJ_eq_map]

def Rel (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) (c : Fin 2 → W) : Prop :=
  s - Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.C (c 0) * MvPowerSeries.X 0 + MvPowerSeries.C (c 1) * MvPowerSeries.X 1) ∈ JJ g ^ 2

theorem rel_iff_sum (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) (c : Fin 2 → W) :
    Rel g s c ↔ s - Ideal.Quotient.mk (Ideal.span {g}) (∑ ii : Fin 2, MvPowerSeries.C (c ii) * MvPowerSeries.X ii) ∈ JJ g ^ 2 := by
  rw [Rel, Fin.sum_univ_two]

theorem exists_rel (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) (hs : s ∈ JJ g) : ∃ c : Fin 2 → W, Rel g s c := by
  rw [JJ_eq_map] at hs
  obtain ⟨φ, hφ, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hs
  refine ⟨![MvPowerSeries.coeff (Finsupp.single 0 1) φ, MvPowerSeries.coeff (Finsupp.single 1 1) φ], ?_⟩
  rw [Rel, JJ_sq_eq_map, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by simpa using sub_lin_mem_sq φ hφ)

theorem rel_X (jj : Fin 2) :
    Rel g (Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.X jj)) (fun ii => (1 : Matrix (Fin 2) (Fin 2) W) ii jj) := by
  rw [Rel]
  simp only [Matrix.one_apply]
  fin_cases jj <;> simp

theorem rel_sub {s s' : MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}} {c c' : Fin 2 → W}
    (h : Rel g s c) (h' : Rel g s' c') : Rel g (s - s') (c - c') := by
  rw [Rel] at h h' ⊢
  have := Ideal.sub_mem _ h h'
  convert this using 1
  simp only [Pi.sub_apply, map_sub, map_add, map_mul]
  ring

end Chart

theorem rel_push {W₀ W : Type} [CommRing W₀] [CommRing W] (g₀ : MvPowerSeries (Fin 2) W₀) (g : MvPowerSeries (Fin 2) W)
    (φ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) →+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}))
    (ρ : W₀ → W) (hφC : ∀ w : W₀, φ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w)))
    (B : Matrix (Fin 2) (Fin 2) W) (hφX : ∀ ii : Fin 2, Rel g (φ (Ideal.Quotient.mk _ (MvPowerSeries.X ii))) (fun kk => B kk ii))
    (s : MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) (c : Fin 2 → W₀) (hs : Rel g₀ s c) :
    Rel g (φ s) (fun kk => ∑ ii : Fin 2, B kk ii * ρ (c ii)) := by

  have hJ : (JJ g₀).map φ ≤ JJ g := by
    rw [JJ, Ideal.map_span, Set.image_pair]
    refine Ideal.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have h0 := hφX 0
      rw [Rel] at h0
      have := Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero h0)
        (show Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.C (B 0 0) * MvPowerSeries.X 0 + MvPowerSeries.C (B 1 0) * MvPowerSeries.X 1) ∈ JJ g from ?_)
      · simpa using this
      · rw [map_add, map_mul, map_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · have h1 := hφX 1
      rw [Rel] at h1
      have := Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero h1)
        (show Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.C (B 0 1) * MvPowerSeries.X 0 + MvPowerSeries.C (B 1 1) * MvPowerSeries.X 1) ∈ JJ g from ?_)
      · simpa using this
      · rw [map_add, map_mul, map_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hJ2 : (JJ g₀ ^ 2).map φ ≤ JJ g ^ 2 := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hJ 2
  have h0 := hφX 0
  have h1 := hφX 1
  rw [Rel] at hs h0 h1 ⊢
  have e1 := hJ2 (Ideal.mem_map_of_mem φ hs)
  have e2 := Ideal.mul_mem_left _ (Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.C (ρ (c 0)))) h0
  have e3 := Ideal.mul_mem_left _ (Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.C (ρ (c 1)))) h1
  have := Ideal.add_mem _ e1 (Ideal.add_mem _ e2 e3)
  convert this using 1
  simp only [map_sub, map_add, map_mul, hφC, Fin.sum_univ_two]
  ring

theorem mem_of_lin_mem_sq (t : W) (I : Ideal W) (ht : t ∈ I) (f u v : MvPowerSeries (Fin 2) W) (hf : f ∈ XX W ^ 2)
    (a b : W)
    (h : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
        (MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1) ∈
      JJ (MvPowerSeries.C t * v - f * u) ^ 2) :
    a ∈ I ∧ b ∈ I := by
  classical
  set g := MvPowerSeries.C t * v - f * u with hg
  rw [JJ_sq_eq_map] at h
  obtain ⟨ψ, hψ, hψeq⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hψeq
  obtain ⟨r, hr⟩ := hψeq

  have hψ0 : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < 2 → MvPowerSeries.coeff n ψ = 0 :=
    (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 2 ψ).mp hψ
  have hfu : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < 2 → MvPowerSeries.coeff n (r * (f * u)) = 0 :=
    (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 2 _).mp
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hf))
  have key : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < 2 →
      MvPowerSeries.coeff n (MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) W) = - (t * MvPowerSeries.coeff n (r * v)) := by
    intro n hn
    have := congrArg (MvPowerSeries.coeff n) hr
    rw [map_sub, hψ0 n hn, zero_sub, hg, mul_sub, map_sub, hfu n hn, sub_zero,
      show r * (MvPowerSeries.C t * v) = MvPowerSeries.C t * (r * v) by ring, MvPowerSeries.coeff_C_mul] at this
    linear_combination this
  constructor
  · have := key (Finsupp.single 0 1) (by simp)
    rw [coeff_lin] at this
    simp [single_zero_ne_single_one] at this
    rw [this]
    exact I.neg_mem (Ideal.mul_mem_right _ _ ht)
  · have := key (Finsupp.single 1 1) (by simp)
    rw [coeff_lin] at this
    simp [single_zero_ne_single_one.symm] at this
    rw [this]
    exact I.neg_mem (Ideal.mul_mem_right _ _ ht)

end

end LinPartTransport

open LinPartTransport in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (t₀ : W₀) (ht₀ : t₀ ∈ IsLocalRing.maximalIdeal W₀) (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (t : W) (ht : t ∈ IsLocalRing.maximalIdeal W) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (β : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (βW : W₀ ≃+* W)
    (hβ : ∀ w : W₀, β (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (βW w)))
    (hβJ : ∀ jj : Fin 2, β (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)})
    (hβJ' : ∀ jj : Fin 2, β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 1)})
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}))
    (σW₀ : W₀ ≃+* W₀) (hσ : ∀ w : W₀, σW₀ w - w ∈ IsLocalRing.maximalIdeal W₀)
    (hsemi₀ : ∀ w : W₀, θ₀ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (σW₀ w)))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)
    (hlin₀ : ∀ jj : Fin 2, θ₀ (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk _ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 1)}) ^ 2) :
    let S := MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
    let θ : S ≃+* S := β.symm.trans (θ₀.trans β)
    let σW : W ≃+* W := βW.symm.trans (σW₀.trans βW)
    ∃ (B : Matrix (Fin 2) (Fin 2) W) (B' : Matrix (Fin 2) (Fin 2) W₀) (M : Matrix (Fin 2) (Fin 2) W),
      (∀ jj : Fin 2, β (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (B ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
      (∀ ii jj : Fin 2, (B * B'.map βW) ii jj - (1 : Matrix (Fin 2) (Fin 2) W) ii jj ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
      (∀ ii jj : Fin 2, M ii jj - (B * M₀.map βW * B'.map βW) ii jj ∈ IsLocalRing.maximalIdeal W) := by
  intro S mkS θ σW
  classical

  have hB : ∀ jj : Fin 2, ∃ c : Fin 2 → W, Rel (MvPowerSeries.C t * v - f * u) (β (Ideal.Quotient.mk _ (MvPowerSeries.X jj))) c :=
    fun jj => exists_rel (MvPowerSeries.C t * v - f * u) _ (hβJ jj)
  choose Bc hBc using hB
  have hB' : ∀ jj : Fin 2, ∃ c : Fin 2 → W₀, Rel (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj))) c :=
    fun jj => exists_rel (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) _ (hβJ' jj)
  choose Bc' hBc' using hB'
  let B : Matrix (Fin 2) (Fin 2) W := fun ii jj => Bc jj ii
  let B' : Matrix (Fin 2) (Fin 2) W₀ := fun ii jj => Bc' jj ii
  have hBrel : ∀ ii : Fin 2, Rel (MvPowerSeries.C t * v - f * u) (β.toRingHom (Ideal.Quotient.mk _ (MvPowerSeries.X ii))) (fun kk => B kk ii) :=
    fun ii => hBc ii
  have hB'rel : ∀ jj : Fin 2, Rel (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj))) (fun ii => B' ii jj) :=
    fun jj => hBc' jj
  have hM₀ : ∀ jj : Fin 2, Rel (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (θ₀.toRingHom (Ideal.Quotient.mk _ (MvPowerSeries.X jj))) (fun ii => M₀ ii jj) :=
    fun jj => (rel_iff_sum (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) _ _).mpr (hlin₀ jj)
  have hβC : ∀ w : W₀, β.toRingHom (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (βW w)) :=
    fun w => hβ w
  have hθ₀C : ∀ w : W₀, θ₀.toRingHom (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (σW₀ w)) :=
    fun w => hsemi₀ w

  have step1 : ∀ jj : Fin 2, Rel (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (θ₀ (β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj))))
      (fun kk => ∑ ii : Fin 2, M₀ kk ii * σW₀ (B' ii jj)) :=
    fun jj => rel_push (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) θ₀.toRingHom σW₀ hθ₀C M₀ hM₀ _ _ (hB'rel jj)
  have step2 : ∀ jj : Fin 2, Rel (MvPowerSeries.C t * v - f * u) (β (θ₀ (β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj)))))
      (fun ll => ∑ kk : Fin 2, B ll kk * βW (∑ ii : Fin 2, M₀ kk ii * σW₀ (B' ii jj))) :=
    fun jj => rel_push (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (MvPowerSeries.C t * v - f * u) β.toRingHom βW hβC B hBrel _ _ (step1 jj)
  have step3 : ∀ jj : Fin 2, Rel (MvPowerSeries.C t * v - f * u) (β (β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj))))
      (fun ll => ∑ kk : Fin 2, B ll kk * βW (B' kk jj)) :=
    fun jj => rel_push (MvPowerSeries.C t₀ * v₀ - f₀ * u₀) (MvPowerSeries.C t * v - f * u) β.toRingHom βW hβC B hBrel _ _ (hB'rel jj)

  have hβW𝔪 : ∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → βW w ∈ IsLocalRing.maximalIdeal W := by
    intro w hw
    by_contra hc
    have hu : IsUnit (βW w) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hc
    have : IsUnit w := by simpa using hu.map βW.symm
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hw)) this
  have hf2 : f ∈ XX W ^ 2 := f_mem_sq q f hf
  let M : Matrix (Fin 2) (Fin 2) W := fun ll jj => ∑ kk : Fin 2, B ll kk * βW (∑ ii : Fin 2, M₀ kk ii * σW₀ (B' ii jj))
  refine ⟨B, B', M, ?_, ?_, ?_, ?_, ?_⟩
  · intro jj
    exact (rel_iff_sum (MvPowerSeries.C t * v - f * u) _ _).mp (hBrel jj)
  · intro ii jj
    have h := step3 jj
    rw [RingEquiv.apply_symm_apply] at h
    have hd := rel_sub (MvPowerSeries.C t * v - f * u) h (rel_X (MvPowerSeries.C t * v - f * u) jj)
    rw [sub_self, LinPartTransport.Rel, zero_sub] at hd
    have hd' := (JJ (MvPowerSeries.C t * v - f * u) ^ 2).neg_mem hd
    rw [neg_neg] at hd'
    obtain ⟨h0, h1⟩ := mem_of_lin_mem_sq t (IsLocalRing.maximalIdeal W) ht f u v hf2 _ _ hd'
    fin_cases ii
    · simp [Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two] at h0 ⊢
      exact h0
    · simp [Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two] at h1 ⊢
      exact h1
  · intro w
    show β (θ₀ (β.symm (mkS (MvPowerSeries.C w)))) = mkS (MvPowerSeries.C (βW (σW₀ (βW.symm w))))
    have h1 : β.symm (mkS (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (βW.symm w)) := by
      apply β.injective
      rw [RingEquiv.apply_symm_apply, hβ, RingEquiv.apply_symm_apply]
    rw [h1, hsemi₀, hβ]
  · intro jj
    have := (rel_iff_sum (MvPowerSeries.C t * v - f * u) _ _).mp (step2 jj)
    exact this
  · intro ii jj
    have e0 := hβW𝔪 _ (hσ (B' 0 jj))
    have e1 := hβW𝔪 _ (hσ (B' 1 jj))
    rw [map_sub] at e0 e1
    have := Ideal.add_mem _
      (Ideal.mul_mem_left _ (B ii 0 * βW (M₀ 0 0) + B ii 1 * βW (M₀ 1 0)) e0)
      (Ideal.mul_mem_left _ (B ii 0 * βW (M₀ 0 1) + B ii 1 * βW (M₀ 1 1)) e1)
    convert this using 1
    simp only [M, Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two, map_add, map_mul]
    ring

end S_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span (solution)
