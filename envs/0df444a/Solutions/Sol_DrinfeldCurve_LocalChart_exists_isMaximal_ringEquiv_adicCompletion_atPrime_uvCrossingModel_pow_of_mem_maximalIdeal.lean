-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/725f92f0-626d-5ad3-a0b6-8029125dcdbb

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace NodeRingSol

section Kside

variable {κ : Type*} [Field κ]

noncomputable def lineSubst (ā : κ) : Fin 2 → MvPowerSeries Unit κ :=
  ![MvPowerSeries.X (), MvPowerSeries.C ā * MvPowerSeries.X ()]

theorem hasSubst_lineSubst (ā : κ) : MvPowerSeries.HasSubst (lineSubst ā) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s <;> simp [lineSubst]

noncomputable def E (ā : κ) : MvPowerSeries (Fin 2) κ →ₐ[κ] MvPowerSeries Unit κ :=
  MvPowerSeries.substAlgHom (hasSubst_lineSubst ā)

theorem E_X_zero (ā : κ) : E ā (X 0) = X () := by
  rw [E, MvPowerSeries.substAlgHom_X]; simp [lineSubst]

theorem E_X_one (ā : κ) : E ā (X 1) = C ā * X () := by
  rw [E, MvPowerSeries.substAlgHom_X]; simp [lineSubst]

theorem E_C (ā c : κ) : E ā (C c) = C c := by
  simp [E, MvPowerSeries.subst_C]

def VanBelow (d : ℕ) (F : MvPowerSeries (Fin 2) κ) : Prop := (d : ℕ∞) ≤ F.order

theorem vanBelow_iff {d : ℕ} {F : MvPowerSeries (Fin 2) κ} :
    VanBelow d F ↔ ∀ c : Fin 2 →₀ ℕ, c.degree < d → coeff c F = 0 := by
  constructor
  · intro h c hc
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hc) h)
  · intro h
    exact MvPowerSeries.nat_le_order h

theorem VanBelow.add {d : ℕ} {F G : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) (hG : VanBelow d G) :
    VanBelow d (F + G) :=
  le_trans (le_min hF hG) MvPowerSeries.min_order_le_add

theorem VanBelow.neg {d : ℕ} {F : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) : VanBelow d (-F) := by
  unfold VanBelow; rwa [MvPowerSeries.order_neg]

theorem VanBelow.sub {d : ℕ} {F G : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) (hG : VanBelow d G) :
    VanBelow d (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem VanBelow.mul {d e : ℕ} {F G : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) (hG : VanBelow e G) :
    VanBelow (d + e) (F * G) := by
  unfold VanBelow at *
  calc ((d + e : ℕ) : ℕ∞) = (d : ℕ∞) + (e : ℕ∞) := by push_cast; rfl
    _ ≤ F.order + G.order := add_le_add hF hG
    _ ≤ (F * G).order := MvPowerSeries.le_order_mul

theorem VanBelow.mono {d e : ℕ} (hde : e ≤ d) {F : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) :
    VanBelow e F :=
  le_trans (by exact_mod_cast hde) hF

theorem VanBelow.zero_left (F : MvPowerSeries (Fin 2) κ) : VanBelow 0 F := by
  unfold VanBelow; simp

theorem VanBelow.mul_right {d : ℕ} {F : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) (G : MvPowerSeries (Fin 2) κ) :
    VanBelow d (F * G) := by
  simpa using hF.mul (VanBelow.zero_left G)

theorem VanBelow.mul_left {d : ℕ} {F : MvPowerSeries (Fin 2) κ} (G : MvPowerSeries (Fin 2) κ) (hF : VanBelow d F) :
    VanBelow d (G * F) := by
  simpa using (VanBelow.zero_left G).mul hF

theorem vanBelow_X (i : Fin 2) : VanBelow 1 (X i : MvPowerSeries (Fin 2) κ) := by
  rw [vanBelow_iff]
  intro c hc
  classical
  rw [MvPowerSeries.coeff_X]
  rw [if_neg]
  rintro rfl
  simp at hc

theorem vanBelow_X_pow (i : Fin 2) (n : ℕ) : VanBelow n ((X i : MvPowerSeries (Fin 2) κ) ^ n) := by
  induction n with
  | zero => exact VanBelow.zero_left _
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul (vanBelow_X i)

def VanT (d : ℕ) (P : MvPowerSeries Unit κ) : Prop := ∀ i : ℕ, i < d → PowerSeries.coeff i P = 0

theorem vanT_E {ā : κ} {d : ℕ} {F : MvPowerSeries (Fin 2) κ} (hF : VanBelow d F) : VanT d (E ā F) := by
  intro i hi
  have hsub : (d : ℕ∞) ≤ (E ā F).order := by
    have h1 : (1 : ℕ∞) ≤ ⨅ s, (lineSubst ā s).order := by
      refine le_iInf fun s => ?_
      refine MvPowerSeries.nat_le_order ?_
      intro c hc
      have hc0 : c = 0 := by
        have : c.degree = 0 := by omega
        exact (Finsupp.degree_eq_zero_iff c).mp this
      subst hc0
      fin_cases s <;> simp [lineSubst]
    have h2 := MvPowerSeries.le_order_subst (hasSubst_lineSubst ā) F
    have h3 : (d : ℕ∞) ≤ (⨅ s, (lineSubst ā s).order) * F.order := by
      calc (d : ℕ∞) = 1 * (d : ℕ∞) := by simp
        _ ≤ (⨅ s, (lineSubst ā s).order) * F.order := mul_le_mul' h1 hF
    have h4 : (E ā F) = F.subst (lineSubst ā) := by
      simp [E]
    rw [h4]
    exact le_trans h3 h2
  have : PowerSeries.coeff i (E ā F) = MvPowerSeries.coeff (Finsupp.single () i) (E ā F) := rfl
  rw [this]
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ hsub
  simp only [Finsupp.degree_single]
  exact_mod_cast hi

theorem coeff_mul_eq_zero_of_vanT {d e n : ℕ} {P Q : MvPowerSeries Unit κ} (hP : VanT d P) (hQ : VanT e Q)
    (hn : n < d + e) : PowerSeries.coeff n (P * Q) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1 < d
  · rw [hP _ h1, zero_mul]
  · have h2 : p.2 < e := by omega
    rw [hQ _ h2, mul_zero]

end Kside

section Oside

variable {O : Type*} [CommRing O] [IsLocalRing O]

open IsLocalRing

noncomputable abbrev bar : MvPowerSeries (Fin 2) O →+* MvPowerSeries (Fin 2) (ResidueField O) :=
  MvPowerSeries.map (residue O)

theorem bar_C_of_mem {c : O} (hc : c ∈ maximalIdeal O) : bar (C c : MvPowerSeries (Fin 2) O) = 0 := by
  rw [MvPowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero]

theorem E_bar_form (q : ℕ) (a : O) (ha : a ^ q - a ∈ maximalIdeal O) :
    E (residue O a) (bar (X 0 * X 1 ^ q - X 0 ^ q * X 1 : MvPowerSeries (Fin 2) O)) = 0 := by
  have hres : residue O a ^ q - residue O a = 0 := by
    rw [← map_pow, ← map_sub, (IsLocalRing.residue_eq_zero_iff _).mpr ha]
  simp only [map_sub, map_mul, map_pow, MvPowerSeries.map_X, E_X_zero, E_X_one]
  have : (C (residue O a) * X () : MvPowerSeries Unit (ResidueField O)) ^ q =
      C (residue O a ^ q) * X () ^ q := by
    rw [mul_pow, map_pow]
  rw [this]
  have key : (X () : MvPowerSeries Unit (ResidueField O)) * (C (residue O a ^ q) * X () ^ q) -
      X () ^ q * (C (residue O a) * X ()) = C (residue O a ^ q - residue O a) * X () ^ (q + 1) := by
    rw [map_sub]; ring
  rw [key, hres, map_zero, zero_mul]

variable (q : ℕ) (a ϖ : O) (f u v : MvPowerSeries (Fin 2) O)

theorem core (hq : 2 ≤ q) (hϖ : ϖ ∈ maximalIdeal O) (ha : a ^ q - a ∈ maximalIdeal O)
    (hu : IsUnit (MvPowerSeries.constantCoeff u))
    (hf : VanBelow (q + 2) (bar (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1))))
    (c : O) (hc : c ∈ maximalIdeal O)
    (k n : ℕ) (m₁ m₂ m₃ m' h : MvPowerSeries (Fin 2) O)
    (hm₂ : VanBelow n (bar m₂)) (hm₃ : VanBelow n (bar m₃))
    (hid : X 0 ^ k * (X 0 ^ (n + 1) + C c * m₁ + X 0 ^ 2 * m₂ + (X 1 - C a * X 0) * m₃) - C c * m' =
      (C (ϖ ^ (q + 1)) * v - f * u) * h) : False := by
  classical
  set κ := ResidueField O
  set ab : κ := residue O a with hab

  have hbar := congrArg bar hid
  have hϖq : ϖ ^ (q + 1) ∈ maximalIdeal O := Ideal.pow_mem_of_mem _ hϖ _ (by omega)
  simp only [map_sub, map_mul, map_add, map_pow, MvPowerSeries.map_X, bar_C_of_mem hϖ, bar_C_of_mem hc,
    zero_mul, add_zero, sub_zero, MvPowerSeries.map_C] at hbar
  rw [zero_pow (Nat.succ_ne_zero q), zero_mul, zero_sub] at hbar

  set L : MvPowerSeries (Fin 2) κ := X 0 ^ (n + 1) + X 0 ^ 2 * bar m₂ + (X 1 - C ab * X 0) * bar m₃ with hL
  have hLvan : VanBelow (n + 1) L := by
    refine VanBelow.add (VanBelow.add (vanBelow_X_pow 0 (n + 1)) ?_) ?_
    · have := (vanBelow_X_pow (κ := κ) 0 2).mul hm₂
      exact this.mono (by omega)
    · have h1 : VanBelow 1 (X 1 - C ab * X 0 : MvPowerSeries (Fin 2) κ) :=
        (vanBelow_X 1).sub ((vanBelow_X 0).mul_left _)
      have := h1.mul hm₃
      exact this.mono (by omega)
  have hXkL : VanBelow (k + (n + 1)) (X 0 ^ k * L) := (vanBelow_X_pow 0 k).mul hLvan

  have hfbar_order : (bar f).order = (q + 1 : ℕ) := by
    rw [MvPowerSeries.order_eq_nat]
    have hform : ∀ c : Fin 2 →₀ ℕ, coeff c (bar f) =
        coeff c (bar (X 0 * X 1 ^ q - X 0 ^ q * X 1)) + coeff c (bar (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1))) := by
      intro c
      rw [← map_add, ← map_add]
      congr 2; ring
    have hformval : bar (X 0 * X 1 ^ q - X 0 ^ q * X 1 : MvPowerSeries (Fin 2) O) =
        monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 - monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
      simp only [map_sub, map_mul, map_pow, MvPowerSeries.map_X]
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
      simp
    constructor
    · refine ⟨Finsupp.single 0 1 + Finsupp.single 1 q, ?_, ?_⟩
      · rw [hform, hformval, map_sub, MvPowerSeries.coeff_monomial_same, MvPowerSeries.coeff_monomial_ne]
        · rw [(vanBelow_iff.mp hf)]
          · simp
          · simp only [map_add, Finsupp.degree_single]; omega
        · intro heq
          have h0 := Finsupp.ext_iff.mp heq 0
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h0
          simp at h0
          omega
      · simp only [map_add, Finsupp.degree_single]; push_cast; ring
    · intro c hc
      rw [hform, hformval, map_sub, (vanBelow_iff.mp hf) c (by omega)]
      rw [MvPowerSeries.coeff_monomial_ne, MvPowerSeries.coeff_monomial_ne]
      · simp
      · rintro rfl; simp only [map_add, Finsupp.degree_single] at hc; omega
      · rintro rfl; simp only [map_add, Finsupp.degree_single] at hc; omega
  have hubar_order : (bar u).order = 0 := by
    have hne : coeff (0 : Fin 2 →₀ ℕ) (bar u) ≠ 0 := by
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_zero_eq_constantCoeff]
      rw [ne_eq, IsLocalRing.residue_eq_zero_iff]
      exact fun hmem => (IsLocalRing.mem_maximalIdeal _ |>.mp hmem) hu
    have := MvPowerSeries.order_le hne
    simpa using this
  have hrel_order : (-(bar f * bar u)).order = (q + 1 : ℕ) := by
    rw [MvPowerSeries.order_neg, MvPowerSeries.order_mul, hfbar_order, hubar_order, add_zero]

  have hErel : VanT (q + 2) (E ab (-(bar f * bar u))) := by
    have hEf : E ab (bar f) = E ab (bar (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1))) := by
      have : bar f = bar (X 0 * X 1 ^ q - X 0 ^ q * X 1) + bar (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1)) := by
        rw [← map_add]; congr 1; ring
      rw [this, map_add, E_bar_form q a ha, zero_add]
    have hv : VanT (q + 2) (E ab (bar f)) := by
      rw [hEf]; exact vanT_E hf
    intro i hi
    rw [map_neg, map_mul, LinearMap.map_neg, neg_eq_zero]
    exact coeff_mul_eq_zero_of_vanT hv (fun _ h => absurd h (Nat.not_lt_zero _)) (by omega)

  have hEh : VanT (k + n - q) (E ab (bar h)) := by
    by_cases hh : bar h = 0
    · intro i _; simp [hh]
    · apply vanT_E
      have hfin := (MvPowerSeries.ne_zero_iff_order_finite.mp hh)

      have h1 : ((k + (n + 1) : ℕ) : ℕ∞) ≤ (-(bar f * bar u) * bar h).order := by
        rw [← hbar]; exact hXkL
      rw [MvPowerSeries.order_mul, hrel_order, ← hfin] at h1
      unfold VanBelow
      rw [← hfin]
      have h2 : k + (n + 1) ≤ (q + 1) + (bar h).order.toNat := by
        exact_mod_cast h1
      exact_mod_cast (show k + n - q ≤ (bar h).order.toNat by omega)

  have hE := congrArg (fun F => PowerSeries.coeff (k + (n + 1)) (E ab F)) hbar
  have hEL : E ab L = X () ^ (n + 1) + X () ^ 2 * E ab (bar m₂) := by
    rw [hL]; simp only [map_add, map_mul, map_sub, map_pow, E_X_zero, E_X_one, E_C]; ring
  have lhs : PowerSeries.coeff (k + (n + 1)) (E ab (X 0 ^ k * L)) = 1 := by
    rw [map_mul (E ab), map_pow (E ab), E_X_zero, hEL]
    change PowerSeries.coeff (k + (n + 1)) (PowerSeries.X ^ k *
      (PowerSeries.X ^ (n + 1) + PowerSeries.X ^ 2 * E ab (bar m₂))) = 1
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show k + (n + 1) - k = n + 1 by omega, map_add,
      PowerSeries.coeff_X_pow_self, PowerSeries.coeff_X_pow_mul']
    split_ifs with h2
    · rw [vanT_E hm₂ (n + 1 - 2) (by omega), add_zero]
    · rw [add_zero]
  have rhs : PowerSeries.coeff (k + (n + 1)) (E ab (-(bar f * bar u) * bar h)) = 0 := by
    rw [map_mul (E ab)]
    exact coeff_mul_eq_zero_of_vanT hErel hEh (by omega)
  rw [lhs, rhs] at hE
  exact one_ne_zero hE

end Oside

section CompletionHelpers

open IsLocalRing

theorem surjective_toQuotPowerSeries {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})).comp
      (PowerSeries.C (R := O))) := by
  set g : Polynomial O := Polynomial.X - Polynomial.C ϖ with hg
  have hgd : g.IsDistinguishedAt (maximalIdeal O) := by
    refine ⟨⟨fun {n} hn => ?_⟩, Polynomial.monic_X_sub_C ϖ⟩
    rw [hg, Polynomial.natDegree_X_sub_C] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    simpa [hg] using hϖ
  have hIJ : Ideal.span {(g : PowerSeries O)} = Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ} := by
    rw [hg, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
  let Φ : O ≃ₐ[O] PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ} :=
    (Polynomial.quotientSpanXSubCAlgEquiv ϖ).symm.trans (hgd.algEquivQuotient.trans (Ideal.quotientEquivAlgOfEq O hIJ))
  intro z
  refine ⟨Φ.symm z, ?_⟩
  have h1 : ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})).comp
      (PowerSeries.C (R := O))) (Φ.symm z) = algebraMap O _ (Φ.symm z) := rfl
  rw [h1, ← Φ.commutes]
  change Φ (Φ.symm z) = z
  exact Φ.apply_symm_apply z

theorem map_surjective_of_surjective {A B : Type*} [CommRing A] [CommRing B] (j : A →+* B) (hj : Function.Surjective j) :
    Function.Surjective (MvPowerSeries.map (σ := Fin 2) j) := by
  intro F
  refine ⟨fun c => (hj (coeff c F)).choose, ?_⟩
  ext c
  rw [MvPowerSeries.coeff_map]
  exact (hj (coeff c F)).choose_spec

end CompletionHelpers

section Chart

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [CommRing K]

open IsLocalRing

structure Setup (q : ℕ) (a ϖ π : O) (f u v : MvPowerSeries (Fin 2) O)
    (πK : MvPowerSeries (Fin 2) O →+* K) (rg : Set K) (x y w : K) : Prop where
  hrg : rg = Set.range πK
  hq : 2 ≤ q
  hϖ : ϖ ∈ maximalIdeal O
  hϖ0 : ϖ ≠ 0
  hmax : maximalIdeal O = Ideal.span {π}
  hϖK : πK (C ϖ) ≠ 0
  hϖreg : ∀ z : K, πK (C ϖ) * z = 0 → z = 0
  ha : a ^ q - a ∈ maximalIdeal O
  hqO : (q : O) ∈ maximalIdeal O
  hu : IsUnit u
  hf : VanBelow (q + 2) (bar (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1)))
  hker : ∀ m, πK m = 0 → ∃ h, m = (C (ϖ ^ (q + 1)) * v - f * u) * h
  hy : y = πK (X 0)
  hxy : x * y = πK (C ϖ)
  hwy : w * y = πK (X 1)
  hconst : ∀ g : MvPowerSeries (Fin 2) O, ∃ r ∈ Subring.closure (rg ∪ {x, w}),
    πK g = πK (C (MvPowerSeries.constantCoeff g)) + y * r
  hrelK : ∃ G ∈ Subring.closure (rg ∪ {x, w}),
    x ^ (q + 1) * πK v = (w ^ q - w + y * G) * πK u
  hnoeth : IsNoetherianRing (Subring.closure (rg ∪ {x, w}))

variable {q : ℕ} {a ϖ π : O} {f u v : MvPowerSeries (Fin 2) O} {πK : MvPowerSeries (Fin 2) O →+* K} {rg : Set K}
  {x y w : K}

namespace Setup

variable (S : Setup q a ϖ π f u v πK rg x y w)
include S

def R₀ (_ : Setup q a ϖ π f u v πK rg x y w) : Subring K := Subring.closure (rg ∪ {x, w})

theorem R₀_def : S.R₀ = Subring.closure (rg ∪ {x, w}) := rfl

theorem πK_mem (m : MvPowerSeries (Fin 2) O) : πK m ∈ S.R₀ :=
  Subring.subset_closure (Or.inl (by rw [S.hrg]; exact ⟨m, rfl⟩))

theorem x_mem : x ∈ S.R₀ := Subring.subset_closure (Or.inr (by simp))

theorem w_mem : w ∈ S.R₀ := Subring.subset_closure (Or.inr (by simp))

theorem y_mem : y ∈ S.R₀ := by
  have h := S.πK_mem (X 0)
  rw [← S.hy] at h
  exact h

theorem c_mem (o : O) : πK (C o) ∈ S.R₀ := S.πK_mem _

theorem πK_C_ϖ_ne_zero : πK (C ϖ) ≠ 0 := S.hϖK

theorem π_mem : π ∈ maximalIdeal O := S.hmax ▸ Ideal.mem_span_singleton_self π

theorem exists_ϖ_eq : ∃ ϖ' : O, ϖ = π * ϖ' := by
  have := S.hϖ; rw [S.hmax, Ideal.mem_span_singleton'] at this
  obtain ⟨c, hc⟩ := this; exact ⟨c, by rw [← hc, mul_comm]⟩

theorem x_ne_zero : x ≠ 0 := by
  intro h0
  apply S.πK_C_ϖ_ne_zero
  rw [← S.hxy, h0, zero_mul]

theorem y_ne_zero : y ≠ 0 := by
  intro h0
  apply S.πK_C_ϖ_ne_zero
  rw [← S.hxy, h0, mul_zero]

def RepAt (_ : Setup q a ϖ π f u v πK rg x y w) (n : ℕ) (r : K) : Prop :=
  ∃ m : MvPowerSeries (Fin 2) O, VanBelow n (bar m) ∧ r * y ^ n = πK m

theorem RepAt.mono {n n' : ℕ} (h : n ≤ n') {r : K} (hr : S.RepAt n r) : S.RepAt n' r := by
  obtain ⟨m, hm, hrm⟩ := hr
  refine ⟨m * X 0 ^ (n' - n), ?_, ?_⟩
  · have := hm.mul (vanBelow_X_pow (κ := ResidueField O) 0 (n' - n))
    rw [show n + (n' - n) = n' by omega] at this
    simpa [map_mul, map_pow, MvPowerSeries.map_X] using this
  · rw [map_mul, map_pow, ← S.hy, ← hrm, mul_assoc, ← pow_add, show n + (n' - n) = n' by omega]

theorem repAt_of_mem {r : K} (hr : r ∈ S.R₀) : ∃ n, S.RepAt n r := by
  refine Subring.closure_induction (p := fun r _ => ∃ n, S.RepAt n r) ?_ ?_ ?_ ?_ ?_ ?_ hr
  · rintro r (hr1 | hr)
    · rw [S.hrg] at hr1
      obtain ⟨m, rfl⟩ := hr1
      exact ⟨0, m, VanBelow.zero_left _, by simp⟩
    · obtain h | h : r = x ∨ r = w := by simpa using hr
      · rw [h]
        refine ⟨1, C ϖ, ?_, by rw [pow_one, S.hxy]⟩
        change VanBelow 1 (bar (C ϖ))
        rw [bar_C_of_mem S.hϖ]; unfold VanBelow; simp
      · rw [h]
        exact ⟨1, X 1, by simpa [MvPowerSeries.map_X] using vanBelow_X (κ := ResidueField O) 1,
          by rw [pow_one, S.hwy]⟩
  · exact ⟨0, 0, VanBelow.zero_left _, by simp⟩
  · exact ⟨0, 1, VanBelow.zero_left _, by simp⟩
  · rintro r r' - - ⟨n, hn⟩ ⟨n', hn'⟩
    obtain ⟨m, hm, hrm⟩ := RepAt.mono S (Nat.le_add_right n n') hn
    obtain ⟨m', hm', hrm'⟩ := RepAt.mono S (Nat.le_add_left n' n) hn'
    exact ⟨n + n', m + m', hm.add hm', by rw [add_mul, hrm, hrm', map_add]⟩
  · rintro r - ⟨n, m, hm, hrm⟩
    exact ⟨n, -m, by simpa using hm.neg, by rw [neg_mul, hrm, map_neg]⟩
  · rintro r r' - - ⟨n, m, hm, hrm⟩ ⟨n', m', hm', hrm'⟩
    refine ⟨n + n', m * m', by simpa using hm.mul hm', ?_⟩
    rw [map_mul, ← hrm, ← hrm']; ring

def X' : S.R₀ := ⟨x, S.x_mem⟩
def Y' : S.R₀ := ⟨y, S.y_mem⟩
def W' : S.R₀ := ⟨w, S.w_mem⟩

def cR : O →+* S.R₀ := (πK.comp (C : O →+* MvPowerSeries (Fin 2) O)).codRestrict S.R₀ (fun o => S.c_mem o)

@[scoped simp] theorem coe_X' : (S.X' : K) = x := rfl
@[scoped simp] theorem coe_Y' : (S.Y' : K) = y := rfl
@[scoped simp] theorem coe_W' : (S.W' : K) = w := rfl
@[scoped simp] theorem coe_cR (o : O) : (S.cR o : K) = πK (C o) := rfl

def 𝔫 : Ideal S.R₀ := Ideal.span {S.cR π, S.Y', S.X', S.W' - S.cR a}

theorem π'_mem : S.cR π ∈ S.𝔫 := Ideal.subset_span (by simp)
theorem X'_mem : S.X' ∈ S.𝔫 := Ideal.subset_span (by simp)
theorem Y'_mem : S.Y' ∈ S.𝔫 := Ideal.subset_span (by simp)
theorem W'_sub_mem : S.W' - S.cR a ∈ S.𝔫 := Ideal.subset_span (by simp)

theorem cR_ϖ : S.cR ϖ = S.X' * S.Y' := Subtype.ext (by simp [S.hxy])

theorem cR_mem_of_mem {o : O} (ho : o ∈ maximalIdeal O) : S.cR o ∈ S.𝔫 := by
  rw [S.hmax, Ideal.mem_span_singleton'] at ho
  obtain ⟨c, rfl⟩ := ho
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ S.π'_mem

theorem mem_𝔫_iff (r : S.R₀) : r ∈ S.𝔫 ↔
    ∃ r₀ r₁ r₂ r₃ : S.R₀, r = r₀ * S.cR π + r₁ * S.X' + r₂ * S.Y' + r₃ * (S.W' - S.cR a) := by
  unfold 𝔫
  constructor
  · intro hr
    rw [Ideal.mem_span_insert] at hr
    obtain ⟨r₀, z, hz, rfl⟩ := hr
    rw [Ideal.mem_span_insert] at hz
    obtain ⟨r₁, z', hz', rfl⟩ := hz
    rw [Ideal.mem_span_pair] at hz'
    obtain ⟨r₂, r₃, rfl⟩ := hz'
    exact ⟨r₀, r₂, r₁, r₃, by ring⟩
  · rintro ⟨r₀, r₂, r₁, r₃, rfl⟩
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem one_notMem : (1 : S.R₀) ∉ S.𝔫 := by
  intro h1
  obtain ⟨r₀, r₁, r₂, r₃, hsum⟩ := (S.mem_𝔫_iff 1).mp h1
  have hsumK := congrArg (fun r : S.R₀ => (r : K)) hsum
  simp only [OneMemClass.coe_one, Subring.coe_add, Subring.coe_mul, coe_X', coe_Y', AddSubgroupClass.coe_sub,
    coe_W', coe_cR] at hsumK
  obtain ⟨n₀, h₀⟩ := S.repAt_of_mem r₀.2
  obtain ⟨n₁, h₁⟩ := S.repAt_of_mem r₁.2
  obtain ⟨n₂, h₂⟩ := S.repAt_of_mem r₂.2
  obtain ⟨n₃, h₃⟩ := S.repAt_of_mem r₃.2
  set N := n₀ + n₁ + n₂ + n₃ with hN
  obtain ⟨m₀, hm₀, e₀⟩ := RepAt.mono S (show n₀ ≤ N by omega) h₀
  obtain ⟨m₁, hm₁, e₁⟩ := RepAt.mono S (show n₁ ≤ N by omega) h₁
  obtain ⟨m₂, hm₂, e₂⟩ := RepAt.mono S (show n₂ ≤ N by omega) h₂
  obtain ⟨m₃, hm₃, e₃⟩ := RepAt.mono S (show n₃ ≤ N by omega) h₃
  obtain ⟨ϖ', hϖ'⟩ := S.exists_ϖ_eq
  have hxy := S.hxy
  have hwy := S.hwy
  have hy := S.hy
  have hϖK' : πK (C ϖ) = πK (C π) * πK (C ϖ') := by rw [← map_mul, ← map_mul, ← hϖ']
  have key : πK (X 0 ^ 0 * (X 0 ^ (N + 1) + C π * (-(X 0 * m₀ + C ϖ' * m₁)) + X 0 ^ 2 * (-m₂) +
      (X 1 - C a * X 0) * (-m₃)) - C π * 0) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_zero, mul_zero, sub_zero, pow_zero, one_mul]
    rw [← hy]
    linear_combination (y ^ (N + 1)) * hsumK + (πK (C π) * y) * e₀ + (x * y) * e₁ + (πK m₁) * hxy +
      (πK m₁) * hϖK' + y ^ 2 * e₂ + (w * y - πK (C a) * y) * e₃ + (πK m₃) * hwy
  obtain ⟨h, hh⟩ := S.hker _ key
  exact core q a ϖ f u v S.hq S.hϖ S.ha ((MvPowerSeries.isUnit_iff_constantCoeff).mp S.hu) S.hf π S.π_mem 0 N
    (-(X 0 * m₀ + C ϖ' * m₁)) (-m₂) (-m₃) 0 h (by simpa using hm₂.neg) (by simpa using hm₃.neg) hh

theorem exists_sub_cR_mem (r : S.R₀) : ∃ o : O, r - S.cR o ∈ S.𝔫 := by
  obtain ⟨r, hr⟩ := r
  refine Subring.closure_induction (p := fun r hr => ∃ o : O, (⟨r, hr⟩ : S.R₀) - S.cR o ∈ S.𝔫)
    ?_ ?_ ?_ ?_ ?_ ?_ hr
  · rintro r (hr1 | hr')
    · have hr1' := hr1
      rw [S.hrg] at hr1'
      obtain ⟨m, rfl⟩ := hr1'
      obtain ⟨r', hr', hm⟩ := S.hconst m
      refine ⟨MvPowerSeries.constantCoeff m, ?_⟩
      have : (⟨πK m, S.πK_mem m⟩ : S.R₀) - S.cR (MvPowerSeries.constantCoeff m) = S.Y' * ⟨r', hr'⟩ :=
        Subtype.ext (by simp [hm])
      rw [show (⟨πK m, Subring.subset_closure (Or.inl hr1)⟩ : S.R₀) = ⟨πK m, S.πK_mem m⟩ from rfl, this]
      exact Ideal.mul_mem_right _ _ S.Y'_mem
    · obtain h | h : r = x ∨ r = w := by simpa using hr'
      · subst h
        refine ⟨0, ?_⟩
        have : (⟨r, Subring.subset_closure (Or.inr hr')⟩ : S.R₀) - S.cR 0 = S.X' :=
          Subtype.ext (by simp)
        rw [this]; exact S.X'_mem
      · subst h
        refine ⟨a, ?_⟩
        have : (⟨r, Subring.subset_closure (Or.inr hr')⟩ : S.R₀) - S.cR a = S.W' - S.cR a :=
          Subtype.ext (by simp)
        rw [this]; exact S.W'_sub_mem
  · refine ⟨0, ?_⟩
    have : (⟨0, zero_mem _⟩ : S.R₀) - S.cR 0 = 0 := Subtype.ext (by simp)
    rw [this]; exact Ideal.zero_mem _
  · refine ⟨1, ?_⟩
    have : (⟨1, one_mem _⟩ : S.R₀) - S.cR 1 = 0 := Subtype.ext (by simp)
    rw [this]; exact Ideal.zero_mem _
  · rintro r r' hr hr' ⟨o, ho⟩ ⟨o', ho'⟩
    refine ⟨o + o', ?_⟩
    have : (⟨r + r', add_mem hr hr'⟩ : S.R₀) - S.cR (o + o') = (⟨r, hr⟩ - S.cR o) + (⟨r', hr'⟩ - S.cR o') := by
      rw [map_add]; apply Subtype.ext; simp; ring
    rw [this]; exact Ideal.add_mem _ ho ho'
  · rintro r hr ⟨o, ho⟩
    refine ⟨-o, ?_⟩
    have : (⟨-r, neg_mem hr⟩ : S.R₀) - S.cR (-o) = -(⟨r, hr⟩ - S.cR o) := by
      rw [map_neg]; apply Subtype.ext; simp; ring
    rw [this]; exact S.𝔫.neg_mem ho
  · rintro r r' hr hr' ⟨o, ho⟩ ⟨o', ho'⟩
    refine ⟨o * o', ?_⟩
    have : (⟨r * r', mul_mem hr hr'⟩ : S.R₀) - S.cR (o * o') =
        ⟨r, hr⟩ * (⟨r', hr'⟩ - S.cR o') + (⟨r, hr⟩ - S.cR o) * S.cR o' := by
      rw [map_mul]; apply Subtype.ext; simp; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ho') (Ideal.mul_mem_right _ _ ho)

def resO : O →+* S.R₀ ⧸ S.𝔫 := (Ideal.Quotient.mk S.𝔫).comp S.cR

theorem resO_surjective : Function.Surjective S.resO := by
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨o, ho⟩ := S.exists_sub_cR_mem r
  refine ⟨o, ?_⟩
  change Ideal.Quotient.mk S.𝔫 (S.cR o) = Ideal.Quotient.mk S.𝔫 r
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [← Ideal.neg_mem_iff, neg_sub]; exact ho

theorem 𝔫_ne_top : S.𝔫 ≠ ⊤ := by
  intro h
  exact S.one_notMem (h ▸ Submodule.mem_top)

theorem ker_resO : RingHom.ker S.resO = maximalIdeal O := by
  symm
  refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    haveI : Nontrivial (S.R₀ ⧸ S.𝔫) := Ideal.Quotient.nontrivial_iff.mpr S.𝔫_ne_top
    exact one_ne_zero
  · intro o ho
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk S.𝔫 (S.cR o) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact S.cR_mem_of_mem ho

theorem isMaximal_𝔫 : S.𝔫.IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  have e : (S.R₀ ⧸ S.𝔫) ≃+* O ⧸ maximalIdeal O :=
    (RingHom.quotientKerEquivOfSurjective S.resO_surjective).symm.trans (Ideal.quotEquivOfEq S.ker_resO)
  exact MulEquiv.isField (Ideal.Quotient.field (maximalIdeal O)).toIsField e.toMulEquiv

theorem mem_𝔫_iff_of_cR (o : O) : S.cR o ∈ S.𝔫 ↔ o ∈ maximalIdeal O := by
  rw [← S.ker_resO, RingHom.mem_ker]
  change _ ↔ Ideal.Quotient.mk S.𝔫 (S.cR o) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]

theorem isPrime_𝔫 : S.𝔫.IsPrime := S.isMaximal_𝔫.isPrime

theorem notMem_of_notMem_of_notMem {h h' : S.R₀} (hh : h ∉ S.𝔫) (hh' : h' ∉ S.𝔫) : h * h' ∉ S.𝔫 :=
  fun hm => (S.isPrime_𝔫.mem_or_mem hm).elim hh hh'

theorem ne_zero_of_notMem {h : S.R₀} (hh : h ∉ S.𝔫) : (h : K) ≠ 0 := by
  intro h0
  apply hh
  have : h = 0 := Subtype.ext h0
  rw [this]; exact Ideal.zero_mem _

scoped instance instIsPrime𝔫 : S.𝔫.IsPrime := S.isPrime_𝔫

abbrev N : Type := Localization.AtPrime S.𝔫

abbrev toN : S.R₀ →+* S.N := algebraMap S.R₀ (Localization.AtPrime S.𝔫)

def NX : S.N := S.toN S.X'
def NY : S.N := S.toN S.Y'
def NW : S.N := S.toN S.W'

def cN : O →+* S.N := S.toN.comp S.cR

theorem cN_eq (o : O) : S.cN o = S.toN (S.cR o) := rfl

theorem NX_mul_NY : S.NX * S.NY = S.cN ϖ := by
  rw [cN_eq, S.cR_ϖ, map_mul]; rfl

scoped instance : IsNoetherianRing S.R₀ := S.hnoeth

theorem isNoetherianRing_N : IsNoetherianRing S.N :=
  IsLocalization.isNoetherianRing S.𝔫.primeCompl _ S.hnoeth

theorem toN_mem_maximalIdeal {r : S.R₀} (hr : r ∈ S.𝔫) : S.toN r ∈ maximalIdeal S.N := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ hr

theorem toN_mem_maximalIdeal_iff (r : S.R₀) : S.toN r ∈ maximalIdeal S.N ↔ r ∈ S.𝔫 :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff S.N S.𝔫 r

theorem isUnit_toN_of_notMem {h : S.R₀} (hh : h ∉ S.𝔫) : IsUnit (S.toN h) :=
  IsLocalization.map_units S.N (⟨h, hh⟩ : S.𝔫.primeCompl)

theorem cN_mem_of_mem {o : O} (ho : o ∈ maximalIdeal O) : S.cN o ∈ maximalIdeal S.N :=
  S.toN_mem_maximalIdeal (S.cR_mem_of_mem ho)

theorem cN_mem_span_of_mem {o : O} (ho : o ∈ maximalIdeal O) : S.cN o ∈ Ideal.span {S.cN π, S.NX, S.NY} := by
  rw [S.hmax, Ideal.mem_span_singleton'] at ho
  obtain ⟨c, rfl⟩ := ho
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem isUnit_πK_u : IsUnit (S.toN ⟨πK u, S.πK_mem u⟩) := by
  obtain ⟨uu, huu⟩ := S.hu
  refine (isUnit_iff_exists_inv.mpr ⟨⟨πK ↑uu⁻¹, S.πK_mem _⟩, Subtype.ext ?_⟩).map S.toN
  change πK u * πK ↑uu⁻¹ = 1
  rw [← huu, ← map_mul, Units.mul_inv, map_one]

theorem W_pow_sub_mem : S.NW ^ q - S.NW ∈ Ideal.span {S.cN π, S.NX, S.NY} := by
  obtain ⟨G, hG, hrel⟩ := S.hrelK
  obtain ⟨U', hU'⟩ := isUnit_iff_exists_inv.mp S.isUnit_πK_u
  set U : S.N := S.toN ⟨πK u, S.πK_mem u⟩ with hU
  set V : S.N := S.toN ⟨πK v, S.πK_mem v⟩ with hV
  set G' : S.N := S.toN ⟨G, hG⟩ with hG'
  have hrelR : (S.X' ^ (q + 1) * ⟨πK v, S.πK_mem v⟩ : S.R₀) = (S.W' ^ q - S.W' + S.Y' * ⟨G, hG⟩) * ⟨πK u, S.πK_mem u⟩ :=
    Subtype.ext (by
      simp only [Subring.coe_mul, Subring.coe_pow, coe_X', AddSubgroupClass.coe_sub, Subring.coe_add, coe_W', coe_Y']
      exact hrel)
  have hrelN : S.NX ^ (q + 1) * V = (S.NW ^ q - S.NW + S.NY * G') * U := by
    have := congrArg S.toN hrelR
    simp only [map_mul, map_pow, map_sub, map_add] at this
    exact this
  have : S.NW ^ q - S.NW = S.NX ^ (q + 1) * V * U' - S.NY * G' := by
    have h1 : (S.NW ^ q - S.NW + S.NY * G') * U * U' = S.NW ^ q - S.NW + S.NY * G' := by
      rw [mul_assoc, hU', mul_one]
    rw [← hrelN] at h1
    rw [h1]; ring
  rw [this]
  refine Ideal.sub_mem _ ?_ ?_
  · rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem NW_sub_mem_span : S.NW - S.cN a ∈ Ideal.span {S.cN π, S.NX, S.NY} := by
  set A := S.cN a with hA
  set G₂ : S.N := ∑ i ∈ Finset.range q, S.NW ^ i * A ^ (q - 1 - i) with hG₂
  have hgeom : G₂ * (S.NW - A) = S.NW ^ q - A ^ q := geom_sum₂_mul _ _ _
  have hG₂mem : G₂ ∈ maximalIdeal S.N := by
    have h1 : G₂ - (q : S.N) * A ^ (q - 1) ∈ Ideal.span {S.NW - A} := by
      have : G₂ - (q : S.N) * A ^ (q - 1) = ∑ i ∈ Finset.range q, A ^ (q - 1 - i) * (S.NW ^ i - A ^ i) := by
        rw [hG₂]
        have hq' : (q : S.N) * A ^ (q - 1) = ∑ i ∈ Finset.range q, A ^ (q - 1 - i) * A ^ i := by
          rw [Finset.sum_congr rfl (g := fun _ => A ^ (q - 1)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          intro i hi
          rw [Finset.mem_range] at hi
          rw [← pow_add]; congr 1; omega
        rw [hq', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
      exact Ideal.mem_span_singleton.mpr (sub_dvd_pow_sub_pow _ _ _)
    have h2 : Ideal.span {S.NW - A} ≤ maximalIdeal S.N := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have : S.NW - A = S.toN (S.W' - S.cR a) := by rw [map_sub]; rfl
      rw [SetLike.mem_coe, this]
      exact S.toN_mem_maximalIdeal S.W'_sub_mem
    have h3 : (q : S.N) * A ^ (q - 1) ∈ maximalIdeal S.N := by
      refine Ideal.mul_mem_right _ _ ?_
      have : (q : S.N) = S.cN q := by simp
      rw [this]; exact S.cN_mem_of_mem S.hqO
    have := Ideal.add_mem _ (h2 h1) h3
    simpa using this
  have hunit : IsUnit (G₂ - 1) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits G₂ (IsLocalRing.mem_maximalIdeal _ |>.mp hG₂mem)
    rw [show G₂ - 1 = -(1 - G₂) by ring]
    exact this.neg
  obtain ⟨Hi, hHi⟩ := isUnit_iff_exists_inv.mp hunit
  have key : S.NW - A = ((S.NW ^ q - S.NW) - (A ^ q - A)) * Hi := by
    have : (S.NW ^ q - S.NW) - (A ^ q - A) = (G₂ - 1) * (S.NW - A) := by rw [sub_mul, hgeom]; ring
    rw [this, mul_comm (G₂ - 1), mul_assoc, hHi, mul_one]
  rw [key]
  refine Ideal.mul_mem_right _ _ (Ideal.sub_mem _ S.W_pow_sub_mem ?_)
  rw [hA, ← map_pow, ← map_sub]
  exact S.cN_mem_span_of_mem S.ha

theorem maximalIdeal_eq : maximalIdeal S.N = Ideal.span {S.cN π, S.NX, S.NY} := by
  apply le_antisymm
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    refine Ideal.span_le.mpr ?_
    rintro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rw [SetLike.mem_coe, Ideal.mem_comap]
    rcases hr with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp [cN_eq])
    · exact Ideal.subset_span (by simp [NY])
    · exact Ideal.subset_span (by simp [NX])
    · have : (algebraMap S.R₀ (Localization.AtPrime S.𝔫)) (S.W' - S.cR a) = S.NW - S.cN a := by
        rw [map_sub]; rfl
      rw [this]; exact S.NW_sub_mem_span
  · rw [Ideal.span_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact S.toN_mem_maximalIdeal S.π'_mem
    · exact S.toN_mem_maximalIdeal S.X'_mem
    · exact S.toN_mem_maximalIdeal S.Y'_mem

theorem NW_sub_mem_maximalIdeal : S.NW - S.cN a ∈ maximalIdeal S.N := by
  have : S.NW - S.cN a = S.toN (S.W' - S.cR a) := by rw [map_sub]; rfl
  rw [this]; exact S.toN_mem_maximalIdeal S.W'_sub_mem

theorem toN_W'_sub_mem_maximalIdeal : S.toN (S.W' - S.cR a) ∈ maximalIdeal S.N :=
  S.toN_mem_maximalIdeal S.W'_sub_mem

theorem exists_unit_of_notMem {h : S.R₀} (hh : h ∉ S.𝔫) : ∃ o : O, IsUnit o ∧ h - S.cR o ∈ S.𝔫 := by
  obtain ⟨o, ho⟩ := S.exists_sub_cR_mem h
  refine ⟨o, ?_, ho⟩
  by_contra hnu
  apply hh
  have hmem : S.cR o ∈ S.𝔫 := S.cR_mem_of_mem ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  have := Ideal.add_mem _ ho hmem
  simpa using this

theorem exists_sub_cN_mem (g : S.N) : ∃ o : O, g - S.cN o ∈ maximalIdeal S.N := by
  obtain ⟨⟨r, s⟩, e3⟩ := IsLocalization.surj S.𝔫.primeCompl g
  dsimp only at e3
  obtain ⟨oᵣ, hoᵣ⟩ := S.exists_sub_cR_mem r
  obtain ⟨oₛ, hoₛu, hoₛ⟩ := S.exists_unit_of_notMem (h := (s : S.R₀)) s.2
  obtain ⟨oi, hoi⟩ := isUnit_iff_exists_inv.mp hoₛu
  refine ⟨oᵣ * oi, ?_⟩
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  set J := maximalIdeal S.N
  have e1 : Ideal.Quotient.mk J (S.toN s) = Ideal.Quotient.mk J (S.cN oₛ) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, cN_eq, ← map_sub]; exact S.toN_mem_maximalIdeal hoₛ
  have e2 : Ideal.Quotient.mk J (S.toN r) = Ideal.Quotient.mk J (S.cN oᵣ) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, cN_eq, ← map_sub]; exact S.toN_mem_maximalIdeal hoᵣ
  have e3' : g * S.toN s = S.toN r := e3
  have e4 : S.cN oₛ * S.cN oi = 1 := by rw [← map_mul, hoi, map_one]
  calc Ideal.Quotient.mk J g
      = Ideal.Quotient.mk J g * (Ideal.Quotient.mk J (S.cN oₛ) * Ideal.Quotient.mk J (S.cN oi)) := by
        rw [← map_mul, e4, map_one, mul_one]
    _ = Ideal.Quotient.mk J (g * S.toN s) * Ideal.Quotient.mk J (S.cN oi) := by
        rw [map_mul, e1]; ring
    _ = Ideal.Quotient.mk J (S.cN (oᵣ * oi)) := by
        rw [e3', e2, ← map_mul, ← map_mul]

theorem NX_ne_zero : S.NX ≠ 0 := by
  intro h0
  have h1 : S.toN S.X' = 0 := h0
  rw [IsLocalization.map_eq_zero_iff S.𝔫.primeCompl] at h1
  obtain ⟨s, hs⟩ := h1
  have : (s : S.R₀) = 0 := by
    apply Subtype.ext
    apply S.hϖreg
    have := congrArg (fun z : S.R₀ => (z : K) * y) hs
    simp only [Subring.coe_mul, coe_X', ZeroMemClass.coe_zero, zero_mul] at this
    rw [← S.hxy]; linear_combination this
  exact s.2 (this ▸ Ideal.zero_mem _)

theorem NY_pow_notMem (k : ℕ) : S.NY ^ k ∉ Ideal.span {S.NX} := by
  intro hk
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hk
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj S.𝔫.primeCompl g
  dsimp only at e

  have h1 : S.toN (S.Y' ^ k * (s : S.R₀)) = S.toN (r * S.X') := by
    rw [map_mul, map_mul, map_pow, ← e]
    have hg' : S.toN S.Y' ^ k = g * S.toN S.X' := hg.symm
    rw [hg']; ring
  rw [IsLocalization.eq_iff_exists S.𝔫.primeCompl] at h1
  obtain ⟨t, ht⟩ := h1

  set h : S.R₀ := (t : S.R₀) * (s : S.R₀) with hh_def
  set r' : S.R₀ := (t : S.R₀) * r with hr'_def
  have hh : h ∉ S.𝔫 := S.notMem_of_notMem_of_notMem t.2 s.2
  have E : (h : K) * y ^ k = (r' : K) * x := by
    have := congrArg (fun z : S.R₀ => (z : K)) ht
    simp only [Subring.coe_mul, Subring.coe_pow, coe_Y', coe_X'] at this
    rw [hh_def, hr'_def, Subring.coe_mul, Subring.coe_mul]
    linear_combination this

  obtain ⟨oₕ, hoₕu, hoₕ⟩ := S.exists_unit_of_notMem hh
  obtain ⟨oi, hoi⟩ := isUnit_iff_exists_inv.mp hoₕu
  have h1mem : h * S.cR oi - 1 ∈ S.𝔫 := by
    have : h * S.cR oi - 1 = (h - S.cR oₕ) * S.cR oi := by
      rw [sub_mul, ← map_mul, hoi, map_one]
    rw [this]; exact Ideal.mul_mem_right _ _ hoₕ
  obtain ⟨r₀, r₁, r₂, r₃, hsum⟩ := (S.mem_𝔫_iff _).mp h1mem
  have hsumK := congrArg (fun z : S.R₀ => (z : K)) hsum
  simp only [AddSubgroupClass.coe_sub, Subring.coe_mul, coe_cR, OneMemClass.coe_one, Subring.coe_add, coe_X',
    coe_Y', coe_W'] at hsumK

  obtain ⟨n₀, h₀⟩ := S.repAt_of_mem r₀.2
  obtain ⟨n₁, h₁⟩ := S.repAt_of_mem r₁.2
  obtain ⟨n₂, h₂⟩ := S.repAt_of_mem r₂.2
  obtain ⟨n₃, h₃⟩ := S.repAt_of_mem r₃.2
  obtain ⟨n₄, h₄⟩ := S.repAt_of_mem (r' * S.cR oi).2
  set N := n₀ + n₁ + n₂ + n₃ + n₄ with hN
  obtain ⟨m₀, -, e₀⟩ := RepAt.mono S (show n₀ ≤ N by omega) h₀
  obtain ⟨m₁, -, e₁⟩ := RepAt.mono S (show n₁ ≤ N by omega) h₁
  obtain ⟨m₂, hm₂, e₂⟩ := RepAt.mono S (show n₂ ≤ N by omega) h₂
  obtain ⟨m₃, hm₃, e₃⟩ := RepAt.mono S (show n₃ ≤ N by omega) h₃
  obtain ⟨m', -, e'⟩ := RepAt.mono S (show n₄ ≤ N by omega) h₄
  simp only [Subring.coe_mul, coe_cR] at e'
  obtain ⟨ϖ', hϖ'⟩ := S.exists_ϖ_eq
  have hxy := S.hxy
  have hwy := S.hwy
  have hy := S.hy
  have hϖK' : πK (C ϖ) = πK (C π) * πK (C ϖ') := by rw [← map_mul, ← map_mul, ← hϖ']
  have key : πK (X 0 ^ (k + 1) * (X 0 ^ (N + 1) + C π * (X 0 * m₀ + C ϖ' * m₁) + X 0 ^ 2 * m₂ + (X 1 - C a * X 0) * m₃) -
      C π * (C ϖ' * m' * X 0)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow]
    rw [← hy, ← e₀, ← e₁, ← e₂, ← e₃, ← e', ← hwy]
    linear_combination (-(y ^ (k + N + 2))) * hsumK + (y ^ (N + 2) * πK (C oi)) * E +
      (-((r₁ : K) * y ^ (k + N + 1) - (r' : K) * πK (C oi) * y ^ (N + 1))) * hϖK' +
      (-((r₁ : K) * y ^ (k + N + 1) - (r' : K) * πK (C oi) * y ^ (N + 1))) * hxy
  obtain ⟨h'', hh''⟩ := S.hker _ key
  exact core q a ϖ f u v S.hq S.hϖ S.ha ((MvPowerSeries.isUnit_iff_constantCoeff).mp S.hu) S.hf π S.π_mem (k + 1) N
    (X 0 * m₀ + C ϖ' * m₁) m₂ m₃ (C ϖ' * m' * X 0) h'' hm₂ hm₃ hh''

theorem NX_mem_nonZeroDivisors : S.NX ∈ nonZeroDivisors S.N := by
  rw [mem_nonZeroDivisors_iff_right]
  intro g hg
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj S.𝔫.primeCompl g
  dsimp only at e
  have h1 : S.toN (r * S.X') = 0 := by
    rw [map_mul, ← e]
    change g * S.toN s * S.NX = 0
    rw [mul_right_comm, hg, zero_mul]
  rw [IsLocalization.map_eq_zero_iff S.𝔫.primeCompl] at h1
  obtain ⟨t, ht⟩ := h1
  have h2 : ((t : S.R₀) * r : S.R₀) = 0 := by
    apply Subtype.ext
    apply S.hϖreg
    have := congrArg (fun z : S.R₀ => (z : K) * y) ht
    simp only [Subring.coe_mul, coe_X', ZeroMemClass.coe_zero, zero_mul] at this
    rw [Subring.coe_mul, ← S.hxy]
    linear_combination this
  have h3 : S.toN r = 0 := by
    have := congrArg S.toN h2
    rw [map_mul, map_zero] at this
    exact (S.isUnit_toN_of_notMem t.2).mul_right_eq_zero.mp this
  have h4 : g * S.toN s = 0 := by rw [e, h3]
  exact (S.isUnit_toN_of_notMem s.2).mul_left_eq_zero.mp h4

theorem two_le_ringKrullDim : 2 ≤ ringKrullDim S.N := by
  have hrad : S.NY ∉ (Ideal.span {S.NX}).radical := fun ⟨k, hk⟩ => S.NY_pow_notMem k hk
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf] at hrad
  push_neg at hrad
  obtain ⟨P, ⟨hXP, hP⟩, hYP⟩ := hrad
  haveI := hP
  have hXP' : S.NX ∈ P := hXP (Ideal.subset_span (by simp))
  have hPmin : P ∉ minimalPrimes S.N := fun hmin =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hXP' hmin S.NX_mem_nonZeroDivisors
  obtain ⟨p₀, hp₀, hp₀P⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
  haveI hp₀' : p₀.IsPrime := hp₀.1.1
  have h01 : p₀ < P := lt_of_le_of_ne hp₀P (fun h => hPmin (h ▸ hp₀))
  have h12 : P < maximalIdeal S.N := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) fun h => hYP ?_
    rw [h, S.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h12
  have e0 : (1 : ℕ∞) ≤ Ideal.height P := le_trans le_add_self e1
  have h2 : (2 : ℕ∞) ≤ (maximalIdeal S.N).height :=
    le_trans (show (2 : ℕ∞) = 1 + 1 by rfl).le (le_trans (add_le_add_left e0 1) e2)
  calc (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ ((maximalIdeal S.N).height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h2
    _ ≤ ringKrullDim S.N := Ideal.height_le_ringKrullDim_of_isPrime

open ModularCurve ModularCurve.UVCrossingModel in

theorem exists_ringEquiv [IsAdicComplete (maximalIdeal O) O] (m : ℕ) (hm : 1 ≤ m) (ε : Oˣ)
    (hε : ϖ = π ^ m * (ε : O)) :
    ∃ ι : AdicCompletion (maximalIdeal S.N) S.N ≃+* UVCrossingModel O (π ^ m),
      (∀ o : O, ι (algebraMap S.N _ (S.cN o)) = const (π ^ m) o) ∧
      (∃ γ : UVCrossingModel O (π ^ m), IsUnit γ ∧ ι (algebraMap S.N _ S.NX) = U (π ^ m) * γ) ∧
      ι (algebraMap S.N _ S.NY) = V (π ^ m) := by
  haveI := S.isNoetherianRing_N
  letI : Algebra O S.N := S.cN.toAlgebra
  have halg : ∀ o, algebraMap O S.N o = S.cN o := fun _ => rfl
  have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr S.hmax
  have hm3 : maximalIdeal S.N = Ideal.span {algebraMap O S.N π, S.NX, S.NY} := by
    rw [S.maximalIdeal_eq, halg]
  have hres : Function.Surjective ((IsLocalRing.residue S.N).comp (algebraMap O S.N)) := by
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨o, ho⟩ := S.exists_sub_cN_mem g
    refine ⟨o, ?_⟩
    change Ideal.Quotient.mk _ (S.cN o) = Ideal.Quotient.mk _ g
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Ideal.neg_mem_iff, neg_sub]
    exact ho
  obtain ⟨θW, θ, hθC, -, hθsurj, hθcomp, hθ0, hθ1⟩ :=
    IsLocalRing.exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span π hirr S.NX S.NY hm3 hres
  set j : O →+* PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C π} :=
    (Ideal.Quotient.mk _).comp (PowerSeries.C (R := O)) with hj
  have hjs : Function.Surjective j := surjective_toQuotPowerSeries π S.π_mem
  set θ₀ := θ.comp (MvPowerSeries.map (σ := Fin 2) j) with hθ₀
  have hθ₀s : Function.Surjective θ₀ := hθsurj.comp (map_surjective_of_surjective j hjs)
  have hθ₀C : ∀ o : O, θ₀ (C o) = algebraMap S.N _ (S.cN o) := by
    intro o
    rw [hθ₀, RingHom.comp_apply, MvPowerSeries.map_C, show θ (C (j o)) = (θ.comp C) (j o) from rfl, hθcomp, hj,
      RingHom.comp_apply, hθC, halg]
  have hθ₀0 : θ₀ (X 0) = algebraMap S.N _ S.NX := by
    rw [hθ₀, RingHom.comp_apply, MvPowerSeries.map_X, hθ0]
  have hθ₀1 : θ₀ (X 1) = algebraMap S.N _ S.NY := by
    rw [hθ₀, RingHom.comp_apply, MvPowerSeries.map_X, hθ1]

  set vN : (AdicCompletion (maximalIdeal S.N) S.N)ˣ :=
    (ε.map (S.cN : O →* S.N)).map (algebraMap S.N (AdicCompletion (maximalIdeal S.N) S.N) : S.N →* _) with hvN
  have hvN' : (vN : AdicCompletion (maximalIdeal S.N) S.N) = algebraMap S.N _ (S.cN (ε : O)) := rfl
  have hcNϖ : S.cN ϖ = S.cN π ^ m * S.cN (ε : O) := by
    rw [← map_pow, ← map_mul]; exact congrArg S.cN hε
  have hrel : θ₀ (X 0) * θ₀ (X 1) = θ₀ (C π) ^ m * (vN : AdicCompletion (maximalIdeal S.N) S.N) := by
    rw [hθ₀0, hθ₀1, hθ₀C, hvN', ← map_pow, ← map_mul, ← map_mul, S.NX_mul_NY, hcNϖ]
  have hdim := IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le S.N S.two_le_ringKrullDim
  obtain ⟨ι, hιC, hιX, hιY⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit π hirr m hm θ₀ hθ₀s vN
      hrel hdim
  refine ⟨ι, fun o => ?_, ⟨ι (vN : AdicCompletion (maximalIdeal S.N) S.N), (vN.isUnit).map ι, ?_⟩, ?_⟩
  · rw [← hθ₀C, hιC]
  · rw [← hθ₀0, hιX]
  · rw [← hθ₀1, hιY]

end Setup
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol.Setup"

end Chart
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol.Setup"

section AsmHelpers

open IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart ModularCurve ModularCurve.UVCrossingModel

theorem vanBelow_bar_of_mem_pow {O : Type*} [CommRing O] [IsLocalRing O] (k : ℕ) (g : MvPowerSeries (Fin 2) O)
    (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ k) : VanBelow k (bar g) := by
  set κ := ResidueField O
  have hmap : bar g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k := by
    have h1 := Ideal.mem_map_of_mem (bar (O := O)) hg
    rw [Ideal.map_pow, Ideal.map_span, Set.image_pair, MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1
  clear hg
  induction k generalizing g with
  | zero => exact VanBelow.zero_left _
  | succ k ih =>
    rw [pow_succ] at hmap
    refine Submodule.mul_induction_on hmap (fun m hm n hn => ?_) (fun F G hF hG => hF.add hG)
    · have hn1 : VanBelow 1 n := by
        obtain ⟨A, B, rfl⟩ := Ideal.mem_span_pair.mp hn
        exact ((vanBelow_X 0).mul_left A).add ((vanBelow_X 1).mul_left B)
      obtain ⟨g', rfl⟩ : ∃ g' : MvPowerSeries (Fin 2) O, bar g' = m :=
        map_surjective_of_surjective _ IsLocalRing.residue_surjective m
      exact (ih g' hm).mul hn1

variable {R : Type*} [CommRing R]

theorem le_order_of_mem_pow (m : ℕ) (g : MvPowerSeries (Fin 2) R)
    (hg : g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} ^ m) : (m : ℕ∞) ≤ g.order := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 : (m : ℕ∞) ≤ a.order := ih a ha
      have h2 : (1 : ℕ∞) ≤ b.order := by
        rw [one_le_order_iff_constCoeff_eq_zero]
        obtain ⟨c₀, c₁, rfl⟩ := Ideal.mem_span_pair.mp hb
        simp
      calc ((m + 1 : ℕ) : ℕ∞) = m + 1 := by push_cast; rfl
        _ ≤ a.order + b.order := add_le_add h1 h2
        _ ≤ (a * b).order := le_order_mul
    · exact le_trans (le_min ha hb) min_order_le_add

theorem exists_eq_C_add_X_mul (g : MvPowerSeries (Fin 2) R) :
    ∃ g₀ g₁, g = C (constantCoeff g) + X 0 * g₀ + X 1 * g₁ := by
  classical
  set h := g - C (constantCoeff g) with hh
  let g₀ : MvPowerSeries (Fin 2) R := fun d => coeff (d + Finsupp.single 0 1) h
  have hX1 : (X 1 : MvPowerSeries (Fin 2) R) ∣ h - X 0 * g₀ := by
    rw [X_dvd_iff]
    intro m hm1
    rw [map_sub, X, coeff_monomial_mul]
    by_cases hm0 : m 0 = 0
    · have hm : m = 0 := by ext t; fin_cases t <;> simp [hm0, hm1]
      subst hm
      simp [hh]
    · have hle : Finsupp.single (0 : Fin 2) 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos hle, one_mul]
      show coeff m h - coeff (m - Finsupp.single 0 1 + Finsupp.single 0 1) h = 0
      rw [tsub_add_cancel_of_le hle, sub_self]
  obtain ⟨g₁, hg₁⟩ := hX1
  refine ⟨g₀, g₁, ?_⟩
  rw [← hg₁, hh]; ring

theorem exists_eq_X_mul_add_of_le_order (n : ℕ) (g : MvPowerSeries (Fin 2) R) (hg : ((n + 1 : ℕ) : ℕ∞) ≤ g.order) :
    ∃ g₀ g₁ : MvPowerSeries (Fin 2) R, g = MvPowerSeries.X 0 * g₀ + MvPowerSeries.X 1 * g₁ ∧
      (n : ℕ∞) ≤ g₀.order ∧ (n : ℕ∞) ≤ g₁.order := by
  classical
  have hcoeff : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d < n + 1 → MvPowerSeries.coeff d g = 0 := fun d hd =>
    MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)
  let g₀ : MvPowerSeries (Fin 2) R := fun d => MvPowerSeries.coeff (d + Finsupp.single 0 1) g
  have hg₀ : ∀ d, MvPowerSeries.coeff d g₀ = MvPowerSeries.coeff (d + Finsupp.single 0 1) g := fun d => rfl

  have hX0g₀ : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m (MvPowerSeries.X 0 * g₀) =
      if m 0 = 0 then 0 else MvPowerSeries.coeff m g := by
    intro m
    rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
    by_cases hm0 : m 0 = 0
    · have : ¬ Finsupp.single (0 : Fin 2) 1 ≤ m := by rw [Finsupp.single_le_iff]; omega
      rw [if_neg this, if_pos hm0]
    · have hle : Finsupp.single (0 : Fin 2) 1 ≤ m := by rw [Finsupp.single_le_iff]; omega
      rw [if_pos hle, if_neg hm0, one_mul, hg₀, tsub_add_cancel_of_le hle]
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣ g - MvPowerSeries.X 0 * g₀ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    rw [map_sub, hX0g₀]
    by_cases hm0 : m 0 = 0
    · have hm : m = 0 := by ext t; fin_cases t <;> simp [hm0, hm1]
      subst hm
      rw [if_pos hm0, sub_zero]
      exact hcoeff 0 (by simp)
    · rw [if_neg hm0, sub_self]
  obtain ⟨g₁, hg₁⟩ := hX1
  refine ⟨g₀, g₁, by rw [← hg₁]; ring, ?_, ?_⟩
  · refine MvPowerSeries.nat_le_order (fun d hd => ?_)
    rw [hg₀]
    exact hcoeff _ (by rw [map_add, Finsupp.degree_single]; omega)
  · refine MvPowerSeries.nat_le_order (fun d hd => ?_)
    have h1 : MvPowerSeries.coeff d g₁ = MvPowerSeries.coeff (d + Finsupp.single 1 1) (MvPowerSeries.X 1 * g₁) := by
      rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, if_pos (by simp), one_mul, add_tsub_cancel_right]
    rw [h1, ← hg₁, map_sub, hX0g₀]
    have h2 : MvPowerSeries.coeff (d + Finsupp.single 1 1) g = 0 :=
      hcoeff _ (by rw [map_add, Finsupp.degree_single]; omega)
    by_cases hd0 : ((d + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) : (Fin 2) → ℕ) 0 = 0
    · rw [if_pos hd0, h2, sub_zero]
    · rw [if_neg hd0, sub_self]

end AsmHelpers
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol.Setup"

section AsmChart

open IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

variable {q : ℕ} [Fact q.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {ϖ : O} (pr : ChartPresentation q O ϖ)

abbrev mkS : MvPowerSeries (Fin 2) O →+* pr.Ring := Ideal.Quotient.mk _

abbrev L : Type := Localization.Away (mkS pr (X 0))

abbrev ιL : pr.Ring →+* L pr := algebraMap pr.Ring (L pr)

def yL : L pr := ιL pr (mkS pr (X 0))
def ϖL : L pr := ιL pr (mkS pr (C ϖ))
def tL : L pr := ϖL pr * IsLocalization.Away.invSelf (S := L pr) (mkS pr (X 0))
def wL : L pr := ιL pr (mkS pr (X 1)) * IsLocalization.Away.invSelf (S := L pr) (mkS pr (X 0))
def R₀L : Subring (L pr) := Subring.closure (Set.range (ιL pr) ∪ {tL pr, wL pr})

omit [IsDiscreteValuationRing O] in
theorem invSelf_mul_yL : IsLocalization.Away.invSelf (S := L pr) (mkS pr (X 0)) * yL pr = 1 := by
  rw [yL, mul_comm]; exact IsLocalization.Away.mul_invSelf (S := L pr) (mkS pr (X 0))

omit [IsDiscreteValuationRing O] in
theorem tL_mul_yL : tL pr * yL pr = ϖL pr := by
  rw [tL, mul_assoc, invSelf_mul_yL, mul_one]

omit [IsDiscreteValuationRing O] in
theorem wL_mul_yL : wL pr * yL pr = ιL pr (mkS pr (X 1)) := by
  rw [wL, mul_assoc, invSelf_mul_yL, mul_one]

omit [IsDiscreteValuationRing O] in
theorem isUnit_yL : IsUnit (yL pr) :=
  isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact invSelf_mul_yL pr⟩

omit [IsDiscreteValuationRing O] in
theorem ι_mem_R₀L (s : pr.Ring) : ιL pr s ∈ R₀L pr :=
  Subring.subset_closure (Or.inl ⟨s, rfl⟩)

omit [IsDiscreteValuationRing O] in
theorem tL_mem_R₀L : tL pr ∈ R₀L pr := Subring.subset_closure (Or.inr (Or.inl rfl))

omit [IsDiscreteValuationRing O] in
theorem wL_mem_R₀L : wL pr ∈ R₀L pr := Subring.subset_closure (Or.inr (Or.inr rfl))

omit [IsDiscreteValuationRing O] in

theorem exists_eq_yL_pow_mul (n : ℕ) :
    ∀ g : MvPowerSeries (Fin 2) O, (n : ℕ∞) ≤ g.order →
      ∃ r ∈ R₀L pr, ιL pr (mkS pr g) = yL pr ^ n * r := by
  induction n with
  | zero =>
    intro g _
    exact ⟨ιL pr (mkS pr g), ι_mem_R₀L pr _, by rw [pow_zero, one_mul]⟩
  | succ n ih =>
    intro g hg
    obtain ⟨g₀, g₁, hsplit, h₀, h₁⟩ := exists_eq_X_mul_add_of_le_order n g hg
    obtain ⟨r₀, hr₀, e₀⟩ := ih g₀ h₀
    obtain ⟨r₁, hr₁, e₁⟩ := ih g₁ h₁
    refine ⟨r₀ + wL pr * r₁, (R₀L pr).add_mem hr₀ ((R₀L pr).mul_mem (wL_mem_R₀L pr) hr₁), ?_⟩
    rw [hsplit, map_add, map_mul, map_mul, map_add, map_mul, map_mul, e₀, e₁, ← wL_mul_yL pr, pow_succ]
    rw [show ιL pr (mkS pr (X 0)) = yL pr from rfl]
    ring

omit [IsDiscreteValuationRing O] in

theorem exists_eq_C_add_yL_mul (g : MvPowerSeries (Fin 2) O) :
    ∃ r ∈ R₀L pr, ιL pr (mkS pr g) = ιL pr (mkS pr (C (MvPowerSeries.constantCoeff g))) + yL pr * r := by
  obtain ⟨g₀, g₁, hsplit⟩ := exists_eq_C_add_X_mul g
  refine ⟨ιL pr (mkS pr g₀) + wL pr * ιL pr (mkS pr g₁),
    (R₀L pr).add_mem (ι_mem_R₀L pr _) ((R₀L pr).mul_mem (wL_mem_R₀L pr) (ι_mem_R₀L pr _)), ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, map_mul, map_mul, map_add, map_add, map_mul, map_mul, ← wL_mul_yL pr]
  rw [show ιL pr (mkS pr (X 0)) = yL pr from rfl]
  ring

omit [IsDiscreteValuationRing O] in

theorem exists_rel_chartX :
    ∃ G ∈ R₀L pr, tL pr ^ (q + 1) * ιL pr (mkS pr pr.v) = (wL pr ^ q - wL pr + yL pr * G) * ιL pr (mkS pr pr.u) := by
  obtain ⟨G, hG, eG⟩ := exists_eq_yL_pow_mul pr (q + 2) (pr.f - drinfeldForm q O)
    (le_order_of_mem_pow (q + 2) _ pr.f_sub_mem)
  refine ⟨G, hG, ?_⟩
  have hrel0 : mkS pr pr.rel = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hf : pr.f = drinfeldForm q O + (pr.f - drinfeldForm q O) := by ring
  have hrel : ιL pr (mkS pr (C (ϖ ^ (q + 1)))) * ιL pr (mkS pr pr.v) =
      (ιL pr (mkS pr (drinfeldForm q O)) + ιL pr (mkS pr (pr.f - drinfeldForm q O))) * ιL pr (mkS pr pr.u) := by
    have h1 : (C (ϖ ^ (q + 1)) * pr.v : MvPowerSeries (Fin 2) O) = pr.rel + pr.f * pr.u := by
      simp only [ChartPresentation.rel]; ring
    rw [← map_mul, ← map_mul, h1, map_add, map_add, hrel0, map_zero, zero_add, ← map_add, ← map_add, ← hf,
      map_mul, map_mul]
  rw [eG] at hrel
  have hϖpow : ιL pr (mkS pr (C (ϖ ^ (q + 1)))) = (tL pr * yL pr) ^ (q + 1) := by
    rw [tL_mul_yL pr, ϖL, ← map_pow, ← map_pow, map_pow C]
  have hform : ιL pr (mkS pr (drinfeldForm q O)) = yL pr ^ (q + 1) * (wL pr ^ q - wL pr) := by
    rw [drinfeldForm, map_sub, map_mul, map_mul, map_pow, map_pow, map_sub, map_mul, map_mul, map_pow, map_pow,
      ← wL_mul_yL pr, show ιL pr (mkS pr (X 0)) = yL pr from rfl]
    ring
  rw [hϖpow, hform] at hrel
  apply ((isUnit_yL pr).pow (q + 1)).mul_left_cancel
  linear_combination hrel

def Radj : Subalgebra pr.Ring (L pr) := Algebra.adjoin pr.Ring ({tL pr, wL pr} : Set (L pr))

def RT : Type := ↥(Radj pr)

scoped instance instCommRingRT : CommRing (RT pr) := inferInstanceAs (CommRing ↥(Radj pr))

scoped instance instAlgebraRT : Algebra pr.Ring (RT pr) := inferInstanceAs (Algebra pr.Ring ↥(Radj pr))

omit [IsDiscreteValuationRing O] in
theorem toSubring_Radj : (Radj pr).toSubring = R₀L pr := by
  rw [Radj, Algebra.adjoin_eq_ring_closure]; rfl

scoped instance finiteType_RT : Algebra.FiniteType pr.Ring (RT pr) :=
  (show Algebra.FiniteType pr.Ring ↥(Radj pr) from
    ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_def.mpr ⟨{tL pr, wL pr}, Set.toFinite _, rfl⟩)⟩)

def eRT : ↥(R₀L pr) ≃+* RT pr where
  toFun x := (show RT pr from (⟨x.1, by
    have h := toSubring_Radj pr
    have : (x : L pr) ∈ (Radj pr).toSubring := by rw [h]; exact x.2
    exact this⟩ : ↥(Radj pr)))
  invFun r := ⟨(show ↥(Radj pr) from r).1, by
    have h := toSubring_Radj pr
    have : ((show ↥(Radj pr) from r) : L pr) ∈ (Radj pr).toSubring := (show ↥(Radj pr) from r).2
    rw [h] at this
    exact this⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem isNoetherianRing_R₀L : IsNoetherianRing ↥(R₀L pr) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) O) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsNoetherianRing pr.Ring := Ideal.Quotient.isNoetherianRing _
  haveI : IsNoetherianRing (RT pr) := Algebra.FiniteType.isNoetherianRing pr.Ring (RT pr)
  exact isNoetherianRing_of_ringEquiv (RT pr) (eRT pr).symm

theorem nontrivial_ring (hϖ : ϖ ∈ maximalIdeal O) : Nontrivial pr.Ring := by
  rw [ChartPresentation.Ring, Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (MvPowerSeries.isUnit_iff_constantCoeff.mp hu)
  have hcf : MvPowerSeries.constantCoeff pr.f = 0 := by
    have h := le_order_of_mem_pow (q + 2) _ pr.f_sub_mem
    have h1 : (1 : ℕ∞) ≤ (pr.f - drinfeldForm q O).order :=
      le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)) h
    have h2 := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mp h1
    have h3 : MvPowerSeries.constantCoeff (drinfeldForm q O) = 0 := by
      simp [drinfeldForm, (Fact.out : q.Prime).ne_zero]
    rw [map_sub, h3, sub_zero] at h2
    exact h2
  have h2 : MvPowerSeries.constantCoeff pr.rel = ϖ ^ (q + 1) * MvPowerSeries.constantCoeff pr.v := by
    simp [ChartPresentation.rel, hcf]
  rw [h2] at h1
  have : IsUnit (ϖ ^ (q + 1)) := isUnit_of_mul_isUnit_left h1
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ hϖ _ (by omega)) this

end AsmChart
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol.Setup"

end NodeRingSol
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol.Setup P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.NodeRingSol"

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart ModularCurve ModularCurve.UVCrossingModel NodeRingSol in

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (ε : Oˣ) (hϖπ : ϖ = π ^ m * (ε : O))
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0) ∈ nonZeroDivisors pr.Ring)
    (hqO : (q : O) ∈ maximalIdeal O) (a : O) (ha : a ^ q - a ∈ maximalIdeal O) :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (X 0))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let y : L := algebraMap S L (mkS (X 0))
    let x : L := ι₀ ϖ * IsLocalization.Away.invSelf (S := L) (mkS (X 0))
    let w : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (X 0))
    let R₀ : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x, w})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R₀) (hx : x ∈ R₀) (hy : y ∈ R₀) (hw : w ∈ R₀)
      (𝔪a : Ideal ↥R₀) (_ : 𝔪a.IsMaximal),
      𝔪a = Ideal.span {⟨ι₀ π, hι₀ π⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨w, hw⟩ - ⟨ι₀ a, hι₀ a⟩} ∧
      x * y = ι₀ ϖ ∧
      IsNoetherianRing (Localization.AtPrime 𝔪a) ∧
      maximalIdeal (Localization.AtPrime 𝔪a) =
        Ideal.span {algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ π, hι₀ π⟩,
          algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨x, hx⟩,
          algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨y, hy⟩} ∧
      algebraMap (↥R₀) (Localization.AtPrime 𝔪a) (⟨w, hw⟩ - ⟨ι₀ a, hι₀ a⟩) ∈ maximalIdeal (Localization.AtPrime 𝔪a) ∧
      (∀ g : Localization.AtPrime 𝔪a, ∃ o : O,
        g - algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ o, hι₀ o⟩ ∈ maximalIdeal (Localization.AtPrime 𝔪a)) ∧
      ∃ ι : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪a)) (Localization.AtPrime 𝔪a) ≃+* UVCrossingModel O (π ^ m),
        (∀ o : O, ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ o, hι₀ o⟩)) =
          const (π ^ m) o) ∧
        (∃ γ : UVCrossingModel O (π ^ m), IsUnit γ ∧
          ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨x, hx⟩)) = U (π ^ m) * γ) ∧
        ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨y, hy⟩)) = V (π ^ m) := by

  have hconst_nzd : ∀ a : O, a ≠ 0 → Ideal.Quotient.mk (Ideal.span {pr.rel}) (C a) ∈ nonZeroDivisors pr.Ring :=
    (DrinfeldCurve.LocalChart.ChartPresentation.mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal q O ϖ hϖ hϖ0 pr).1
  haveI : Nontrivial pr.Ring := nontrivial_ring pr hϖ
  intro S mkS' L' ι₀ y x w R₀
  set πK : MvPowerSeries (Fin 2) O →+* L' := (algebraMap pr.Ring L').comp (Ideal.Quotient.mk _) with hπK
  have hpow : Submonoid.powers (Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0)) ≤ nonZeroDivisors pr.Ring :=
    Submonoid.powers_le.mpr hnzd
  have hinj : Function.Injective (algebraMap pr.Ring L') := IsLocalization.injective L' hpow
  have hrange : Set.range (algebraMap pr.Ring L') = Set.range πK := by
    rw [hπK, RingHom.coe_comp, Set.range_comp, Set.range_eq_univ.mpr Ideal.Quotient.mk_surjective, Set.image_univ]
  have hR₀L : NodeRingSol.R₀L pr = R₀ := rfl
  have Sx : NodeRingSol.Setup q a ϖ π pr.f pr.u pr.v πK (Set.range (algebraMap S L')) x y w :=
    { hrg := hrange
      hq := (Fact.out : q.Prime).two_le
      hϖ := hϖ
      hϖ0 := hϖ0
      hmax := hπ
      hϖK := by
        intro h0
        have h1 : Ideal.Quotient.mk (Ideal.span {pr.rel}) (C ϖ) = 0 := hinj (by rw [map_zero]; exact h0)
        exact nonZeroDivisors.ne_zero (hconst_nzd ϖ hϖ0) h1
      hϖreg := by
        intro z hz
        have hmem : πK (C ϖ) ∈ nonZeroDivisors L' :=
          IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0))) L'
            (hconst_nzd ϖ hϖ0)
        exact (mem_nonZeroDivisors_iff_right.mp hmem) z (by rw [mul_comm]; exact hz)
      ha := ha
      hqO := hqO
      hu := pr.isUnit_u
      hf := NodeRingSol.vanBelow_bar_of_mem_pow (q + 2) _ pr.f_sub_mem
      hker := by
        intro m hm
        have h1 : Ideal.Quotient.mk (Ideal.span {pr.rel}) m = 0 := hinj (by rw [map_zero]; exact hm)
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
        obtain ⟨h, hh⟩ := h1
        exact ⟨h, by rw [← hh, mul_comm]; rfl⟩
      hy := rfl
      hxy := NodeRingSol.tL_mul_yL pr
      hwy := NodeRingSol.wL_mul_yL pr
      hconst := fun g => NodeRingSol.exists_eq_C_add_yL_mul pr g
      hrelK := NodeRingSol.exists_rel_chartX pr
      hnoeth := NodeRingSol.isNoetherianRing_R₀L pr }
  obtain ⟨ι, hιC, hιX, hιY⟩ := Sx.exists_ringEquiv m hm ε hϖπ
  exact ⟨Sx.c_mem, Sx.x_mem, Sx.y_mem, Sx.w_mem, Sx.𝔫, Sx.isMaximal_𝔫, rfl, Sx.hxy, Sx.isNoetherianRing_N,
    Sx.maximalIdeal_eq, Sx.toN_W'_sub_mem_maximalIdeal, Sx.exists_sub_cN_mem, ι, hιC, hιX, hιY⟩

end
end S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal (solution)
