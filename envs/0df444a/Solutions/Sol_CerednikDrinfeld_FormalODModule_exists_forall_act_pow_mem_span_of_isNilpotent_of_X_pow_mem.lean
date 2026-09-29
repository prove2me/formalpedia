-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c9406474-715e-59dc-b762-20a83288ce27

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KilledKit

variable {A : Type} [CommRing A] {d : ℕ}

noncomputable abbrev 𝔪 (A : Type) [CommRing A] (d : ℕ) : Ideal (MvPowerSeries (Fin d) A) :=
  Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A))

theorem eq_zero_or_single_of_degree_lt_two (e : Fin d →₀ ℕ) (he : e.degree < 2) :
    e = 0 ∨ ∃ j, e = Finsupp.single j 1 := by
  by_cases h0 : e.degree = 0
  · exact Or.inl ((Finsupp.degree_eq_zero_iff e).mp h0)
  · right
    have h1 : e.degree = 1 := by omega
    have hmem : e ∈ {d' : Fin d →₀ ℕ | d'.degree = 1} := h1
    rw [← Finsupp.range_single_one] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩

theorem mem_𝔪_sq (G : MvPowerSeries (Fin d) A) (h0 : constantCoeff G = 0)
    (h1 : ∀ j, coeff (Finsupp.single j 1) G = 0) : G ∈ 𝔪 A d ^ 2 :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 2 G (fun m hm => by
    rcases eq_zero_or_single_of_degree_lt_two m hm with rfl | ⟨j, rfl⟩
    · exact h0
    · exact h1 j)

theorem nthSeries_sub_mem_𝔪_sq (F : MvFormalGroup d A) (m : ℕ) (i : Fin d) :
    F.nthSeries m i - (m : A) • X i ∈ 𝔪 A d ^ 2 := by
  classical
  refine mem_𝔪_sq _ ?_ (fun j => ?_)
  · rw [map_sub, MvFormalGroup.constantCoeff_nthSeries, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero, sub_zero]
  · have h := congrFun (congrFun (MvFormalGroup.linearPart_nthSeries F m) i) j
    simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply] at h
    rw [map_sub, h, coeff_smul, coeff_X]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h' => hij (Finsupp.single_left_injective one_ne_zero h').symm)]
      simp

section NilEval
variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {C : Type} [CommRing C] [Algebra B C]

noncomputable abbrev bnd (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

theorem le_bnd_iff (n : ℕ) (m : σ →₀ ℕ) : m ≤ bnd σ n ↔ ∀ i, m i ≤ n := by
  simp [bnd, Finsupp.le_def]

theorem prod_pow_eq_zero (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (m : σ →₀ ℕ) (hm : ¬ m ≤ bnd σ n) : (m.prod fun i k => a i ^ k) = 0 := by
  rw [le_bnd_iff] at hm
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  rw [Finsupp.prod]
  have hi' : i ∈ m.support := by
    rw [Finsupp.mem_support_iff]; omega
  apply Finset.prod_eq_zero hi'
  have : a i ^ (n + 1) = 0 := by
    have := Ideal.pow_mem_pow (ha i) (n + 1)
    rwa [hJ, Ideal.mem_bot] at this
  rw [show m i = (n + 1) + (m i - (n + 1)) by omega, pow_add, this, zero_mul]

theorem aeval_eq_zero_of_coeff (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (P : MvPolynomial σ B) (hP : ∀ m, m ≤ bnd σ n → P.coeff m = 0) : MvPolynomial.aeval a P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m ≤ bnd σ n
  · rw [hP m hm, map_zero, zero_mul]
  · rw [← Finsupp.prod, prod_pow_eq_zero J n hJ a ha m hm, mul_zero]

theorem nilEval_def (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → C) :
    MvFormalGroup.nilEval n φ a = MvPolynomial.aeval a (trunc' B (bnd σ n) φ) := rfl

theorem nilEval_add (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ + ψ) a = MvFormalGroup.nilEval n φ a + MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_add]
  congr 1
  ext m
  simp only [coeff_trunc', MvPolynomial.coeff_add, map_add]

theorem nilEval_mul (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ * ψ) a = MvFormalGroup.nilEval n φ a * MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_mul, ← sub_eq_zero, ← map_sub]
  apply aeval_eq_zero_of_coeff J n hJ a ha
  intro m hm
  rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos hm, MvPolynomial.coeff_mul, coeff_mul, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro x hx
  have hx1 : x.1 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_self_add) hm
  have hx2 : x.2 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_add_self) hm
  rw [coeff_trunc', coeff_trunc', if_pos hx1, if_pos hx2]

theorem nilEval_C (n : ℕ) (a : σ → C) (b : B) :
    MvFormalGroup.nilEval n (MvPowerSeries.C b) a = algebraMap B C b := by
  rw [nilEval_def]
  have : trunc' B (bnd σ n) (MvPowerSeries.C b) = MvPolynomial.C b := by
    ext m
    rw [coeff_trunc', MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg (show ¬ (0 = m) from fun h => h0 h.symm)]
      all_goals (split_ifs <;> rfl)
  rw [this, MvPolynomial.aeval_C]

noncomputable def nilEvalRingHom (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvPowerSeries σ B →+* C where
  toFun φ := MvFormalGroup.nilEval n φ a
  map_one' := by rw [show (1 : MvPowerSeries σ B) = MvPowerSeries.C 1 from (map_one _).symm, nilEval_C, map_one]
  map_mul' φ ψ := nilEval_mul J n hJ a ha φ ψ
  map_zero' := by rw [show (0 : MvPowerSeries σ B) = MvPowerSeries.C 0 from (map_zero _).symm, nilEval_C, map_zero]
  map_add' φ ψ := nilEval_add n a φ ψ

theorem nilEvalRingHom_apply (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (φ : MvPowerSeries σ B) : nilEvalRingHom J n hJ a ha φ = MvFormalGroup.nilEval n φ a := rfl

theorem nilEval_mem (J : Ideal C) (k : ℕ) (φ : MvPowerSeries σ B) (hφ : MvPowerSeries.constantCoeff φ = 0)
    (a : σ → C) (ha : ∀ j, a j ∈ J) : MvFormalGroup.nilEval k φ a ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold MvFormalGroup.nilEval
  have hz : (fun j => (Ideal.Quotient.mk J) (a j)) = 0 :=
    funext fun j => Ideal.Quotient.eq_zero_iff_mem.mpr (ha j)
  have h := congrArg (fun ψ => ψ (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => k) φ))
    (MvPolynomial.comp_aeval a (Ideal.Quotient.mkₐ B J))
  simp only [AlgHom.comp_apply] at h
  rw [Ideal.Quotient.mkₐ_eq_mk] at h
  have hc : MvPolynomial.constantCoeff (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => k) φ) =
      MvPowerSeries.constantCoeff φ := by
    show MvPolynomial.coeff 0 _ = MvPowerSeries.coeff 0 φ
    rw [MvPowerSeries.coeff_trunc']; simp
  rw [h, hz, MvPolynomial.aeval_zero, hc, hφ, map_zero]

theorem adicEval_bot_eq_nilEval (J : Ideal C) (m : ℕ) (hJ : J ^ (m + 1) = ⊥) (s : σ → C) (hs : ∀ i, s i ∈ J)
    (G : MvPowerSeries σ B) :
    MvFormalGroup.adicEval (⊥ : Ideal C) s G = MvFormalGroup.nilEval m G s := by
  classical
  let J₀ : Ideal C := Ideal.span (Set.range s)
  have hJ₀le : J₀ ≤ J := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  have hJ₀ : J₀ ^ (m + 1) = ⊥ := le_bot_iff.mp ((Ideal.pow_right_mono hJ₀le _).trans hJ.le)
  have hs₀ : ∀ i, s i ∈ J₀ := fun i => Ideal.subset_span ⟨i, rfl⟩
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J₀ m hJ₀ G s hs₀]
  haveI : IsAdicComplete J₀ C := by
    haveI : IsHausdorff J₀ C := ⟨fun x hx => by
      have := hx (m + 1)
      rw [hJ₀] at this
      simpa [SModEq.zero] using this⟩
    haveI : IsPrecomplete J₀ C := ⟨fun {f} hf => ⟨f (m + 1), fun k => by
      by_cases hk : k ≤ m + 1
      · exact hf hk
      · push Not at hk
        have h1 : f (m + 1) ≡ f k [SMOD (J₀ ^ (m + 1) • ⊤ : Submodule C C)] := hf hk.le
        have h2 : (J₀ ^ k • ⊤ : Submodule C C) = ⊥ := by
          rw [show k = (m + 1) + (k - (m + 1)) by omega, pow_add, hJ₀, Ideal.bot_mul]; simp
        have h3 : (J₀ ^ (m + 1) • ⊤ : Submodule C C) = ⊥ := by rw [hJ₀]; simp
        rw [h2]; rw [h3] at h1
        exact h1.symm⟩⟩
    exact ⟨⟩
  have hrad : ∀ i, s i ∈ J₀.radical := fun i => Ideal.le_radical (hs₀ i)
  have h := MvFormalGroup.map_adicEval (R := B) J₀ (⊥ : Ideal C) (AlgHom.id B C)
    (Submodule.fg_span (Set.finite_range s)) (fun x hx => ⟨m + 1, by
      rw [AlgHom.id_apply]
      have := Ideal.pow_mem_pow hx (m + 1); rwa [hJ₀] at this⟩) hrad G
  rw [AlgHom.id_apply] at h
  exact h.symm

end NilEval

theorem mul_mem_sq_sup {C : Type} [CommRing C] (I P : Ideal C) {x y : C} (hx : x ∈ I ⊔ P) (hy : y ∈ I ⊔ P) :
    x * y ∈ I ^ 2 ⊔ P := by
  obtain ⟨i₁, hi₁, q₁, hq₁, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨i₂, hi₂, q₂, hq₂, rfl⟩ := Submodule.mem_sup.mp hy
  have : (i₁ + q₁) * (i₂ + q₂) = i₁ * i₂ + (i₁ * q₂ + q₁ * (i₂ + q₂)) := by ring
  rw [this]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [pow_two]; exact Ideal.mul_mem_mul hi₁ hi₂
  · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)

end KilledKit

open KilledKit in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B))
    (X : FormalODModule p B) (ρ : Series B)
    (hK : ∃ K : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ K ∈ Ideal.span (Set.range ρ)) :
    ∃ N : ℕ, ∀ i : Fin 2, X.act ((p : Zp2 p) ^ N) i ∈ Ideal.span (Set.range ρ) := by
  classical
  obtain ⟨K, hKx⟩ := hK
  obtain ⟨M, hM⟩ := hB
  set I : Ideal (MvPowerSeries (Fin 2) B) := Ideal.span (Set.range ρ) with hI
  let C : Type := MvPowerSeries (Fin 2) B ⧸ I
  let mk : MvPowerSeries (Fin 2) B →ₐ[B] C := Ideal.Quotient.mkₐ B I
  let xb : Fin 2 → C := fun i => mk (MvPowerSeries.X i)

  have hxb : ∀ i, IsNilpotent (xb i) := fun i => ⟨K, by
    change mk (MvPowerSeries.X i) ^ K = 0
    rw [← map_pow]; exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hKx i)⟩
  let 𝔫 : Ideal C := Ideal.span (Set.range xb)
  have h𝔫fg : 𝔫.FG := Submodule.fg_span (Set.finite_range xb)
  have h𝔫nil : IsNilpotent 𝔫 := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical h𝔫fg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxb i
  obtain ⟨L₀, hL₀⟩ := h𝔫nil
  set L : ℕ := L₀ with hL
  have h𝔫L : 𝔫 ^ (L + 1) = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hL₀]; exact Ideal.pow_le_pow_right (by omega)
  have hxb𝔫 : ∀ i, xb i ∈ 𝔫 := fun i => Ideal.subset_span ⟨i, rfl⟩

  have hev : ∀ G, mk G = MvFormalGroup.nilEval L G xb := by
    intro G
    have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal C) mk
      (fun i => by obtain ⟨k, hk⟩ := hxb i; exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩) G
    rw [h1]
    exact adicEval_bot_eq_nilEval 𝔫 L h𝔫L xb hxb𝔫 G

  let v : ℕ → Fin 2 → C := fun r i => MvFormalGroup.nilEval L (X.F.nthSeries (p ^ r) i) xb
  have hv𝔫 : ∀ r i, v r i ∈ 𝔫 := fun r i =>
    nilEval_mem 𝔫 L _ (MvFormalGroup.constantCoeff_nthSeries X.F _ i) xb hxb𝔫

  have hrec : ∀ r i, v (r + 1) i = MvFormalGroup.nilEval L (X.F.nthSeries p i) (v r) := by
    intro r i
    have hcomp : X.F.nthSeries (p ^ (r + 1)) = Series.comp (X.F.nthSeries p) (X.F.nthSeries (p ^ r)) := by
      rw [← X.act_natCast, ← X.act_natCast, ← X.act_natCast, ← X.act_mul, ← Nat.cast_mul, ← pow_succ']
    change MvFormalGroup.nilEval L (X.F.nthSeries (p ^ (r + 1)) i) xb = _
    rw [hcomp]
    change MvFormalGroup.nilEval L (MvPowerSeries.subst (X.F.nthSeries (p ^ r)) (X.F.nthSeries p i)) xb = _
    exact (MvFormalGroup.nilEval_subst_of_mem 𝔫 L h𝔫L xb hxb𝔫 (X.F.nthSeries (p ^ r))
      (MvFormalGroup.constantCoeff_nthSeries X.F _) (X.F.nthSeries p i)).2

  have hstep : ∀ (J : Ideal C) (s : Fin 2 → C), (∀ i, s i ∈ J) → (∀ i, s i ∈ 𝔫) →
      ∀ i, MvFormalGroup.nilEval L (X.F.nthSeries p i) s ∈ Ideal.span {(p : C)} * J ⊔ J * J := by
    intro J s hsJ hs𝔫 i
    have hsplit : X.F.nthSeries p i = (p : B) • MvPowerSeries.X i + (X.F.nthSeries p i - (p : B) • MvPowerSeries.X i) := by
      rw [add_sub_cancel]
    rw [hsplit, nilEval_add]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [smul_eq_C_mul, nilEval_mul 𝔫 L h𝔫L s hs𝔫, nilEval_C, MvFormalGroup.nilEval_X_of_mem 𝔫 L h𝔫L s hs𝔫 i,
        map_natCast]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hsJ i)
    ·
      have hR := nthSeries_sub_mem_𝔪_sq X.F p i
      have hmap : (𝔪 B 2).map (nilEvalRingHom 𝔫 L h𝔫L s hs𝔫 : MvPowerSeries (Fin 2) B →+* C) ≤ J := by
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        show MvFormalGroup.nilEval L (MvPowerSeries.X j) s ∈ J
        rw [MvFormalGroup.nilEval_X_of_mem 𝔫 L h𝔫L s hs𝔫 j]
        exact hsJ j
      have h2 : (𝔪 B 2 ^ 2).map (nilEvalRingHom 𝔫 L h𝔫L s hs𝔫 : MvPowerSeries (Fin 2) B →+* C) ≤ J * J := by
        rw [Ideal.map_pow, pow_two]; exact Ideal.mul_mono hmap hmap
      exact h2 (Ideal.mem_map_of_mem _ hR)

  let P : Ideal C := Ideal.span {(p : C)}
  have hstage1 : ∀ r i, v r i ∈ 𝔫 ^ (2 ^ r) ⊔ P := by
    intro r
    induction r with
    | zero =>
      intro i
      refine Submodule.mem_sup_left ?_
      rw [pow_zero, pow_one]
      change MvFormalGroup.nilEval L (X.F.nthSeries 1 i) xb ∈ 𝔫
      exact hv𝔫 0 i
    | succ r ih =>
      intro i
      rw [hrec]
      have h := hstep (𝔫 ^ (2 ^ r) ⊔ P) (v r) ih (hv𝔫 r) i
      refine (sup_le ?_ ?_ : Ideal.span {(p : C)} * (𝔫 ^ 2 ^ r ⊔ P) ⊔ (𝔫 ^ 2 ^ r ⊔ P) * (𝔫 ^ 2 ^ r ⊔ P) ≤ 𝔫 ^ 2 ^ (r + 1) ⊔ P) h
      · exact (Ideal.mul_le_left).trans le_sup_right
      · rw [Ideal.mul_le]
        intro x hx y hy
        have := mul_mem_sq_sup (𝔫 ^ 2 ^ r) P hx hy
        rwa [← pow_mul, ← pow_succ] at this

  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, L + 1 ≤ 2 ^ r₀ := ⟨L + 1, Nat.lt_two_pow_self.le⟩
  have hstage1' : ∀ i, v r₀ i ∈ P := by
    intro i
    have h := hstage1 r₀ i
    have hz : 𝔫 ^ (2 ^ r₀) = ⊥ := le_bot_iff.mp ((Ideal.pow_le_pow_right hr₀).trans h𝔫L.le)
    rwa [hz, bot_sup_eq] at h

  have hstage2 : ∀ k i, v (r₀ + k) i ∈ Ideal.span {(p : C) ^ (k + 1)} := by
    intro k
    induction k with
    | zero =>
      intro i
      have h := hstage1' i
      have hPe : Ideal.span {(p : C) ^ (0 + 1)} = P := by rw [zero_add, pow_one]
      rw [hPe]
      exact h
    | succ k ih =>
      intro i
      rw [← add_assoc, hrec]
      have h := hstep (Ideal.span {(p : C) ^ (k + 1)}) (v (r₀ + k)) ih (hv𝔫 _) i
      refine (sup_le ?_ ?_ : Ideal.span {(p : C)} * Ideal.span {(p : C) ^ (k + 1)} ⊔
        Ideal.span {(p : C) ^ (k + 1)} * Ideal.span {(p : C) ^ (k + 1)} ≤ Ideal.span {(p : C) ^ (k + 1 + 1)}) h
      · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_span_singleton]
        exact ⟨1, by ring⟩
      · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_span_singleton, ← pow_add]
        exact pow_dvd_pow _ (by omega)
  refine ⟨r₀ + M, fun i => ?_⟩
  have hzero : v (r₀ + M) i = 0 := by
    have h := hstage2 M i
    have hz : (p : C) ^ (M + 1) = 0 := by
      rw [pow_succ, ← map_natCast (algebraMap B C), ← map_pow, hM, map_zero, zero_mul]
    rw [hz, Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact (Submodule.mem_bot _).mp h
  rw [← Nat.cast_pow, X.act_natCast, ← Ideal.Quotient.eq_zero_iff_mem]
  change mk (X.F.nthSeries (p ^ (r₀ + M)) i) = 0
  rw [hev]
  exact hzero

end S_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem (solution)
