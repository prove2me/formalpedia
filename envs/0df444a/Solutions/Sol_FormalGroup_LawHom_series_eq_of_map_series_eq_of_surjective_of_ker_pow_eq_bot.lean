-- Prove2me | solution 1 for FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6313690e-6e15-584e-9de6-2ce4f03b1992

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
import Theorems.Thm_FormalGroup_LawHom_subst_nthSeries_series_eq
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot

set_option autoImplicit false

namespace R1aAux

open PowerSeries

theorem coeff_X_pow_mul_pow {T : Type*} [CommRing T] (w : PowerSeries T) (M m m₀ : ℕ) (hM : 0 < M) :
    PowerSeries.coeff (m₀ * M) ((PowerSeries.X ^ M * w) ^ m) =
      if m = m₀ then (PowerSeries.constantCoeff w) ^ m₀ else
        if m < m₀ then PowerSeries.coeff (m₀ * M - m * M) (w ^ m) else 0 := by
  rw [mul_pow, ← pow_mul, mul_comm M m, PowerSeries.coeff_X_pow_mul']
  by_cases hmm : m = m₀
  · subst hmm
    rw [if_pos (le_refl _), if_pos rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  · rw [if_neg hmm]
    by_cases hlt : m < m₀
    · rw [if_pos (Nat.mul_le_mul_right M hlt.le), if_pos hlt]
    · have hgt : m₀ < m := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hmm)
      rw [if_neg hlt, if_neg]
      intro hle
      exact absurd (Nat.le_of_mul_le_mul_right hle hM) (not_le.mpr hgt)

theorem coeff_pow_eq_zero_of_lt {T : Type*} [CommRing T] (s : PowerSeries T)
    (hs0 : PowerSeries.constantCoeff s = 0) {m n : ℕ} (h : n < m) : PowerSeries.coeff n (s ^ m) = 0 := by
  obtain ⟨s', hs'⟩ := PowerSeries.X_dvd_iff.mpr hs0
  rw [hs', mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr h)]

theorem cancel {T : Type*} [CommRing T] (I : Ideal T) (s d : PowerSeries T) (M j : ℕ) (hM : 0 < M)
    (hs0 : PowerSeries.constantCoeff s = 0)
    (hsI : ∀ i < M, PowerSeries.coeff i s ∈ I) (hsM : IsUnit (PowerSeries.coeff M s))
    (hd : ∀ m, PowerSeries.coeff m d ∈ I ^ j)
    (hds : ∀ m, PowerSeries.coeff m (PowerSeries.subst s d) ∈ I ^ (j + 1)) :
    ∀ m, PowerSeries.coeff m d ∈ I ^ (j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  let m₀ := Nat.find hcon
  have hm₀ : PowerSeries.coeff m₀ d ∉ I ^ (j + 1) := Nat.find_spec hcon
  have hmin : ∀ m < m₀, PowerSeries.coeff m d ∈ I ^ (j + 1) := fun m hm => by
    by_contra h; exact Nat.find_min hcon hm h
  set K : Ideal T := I ^ (j + 1) with hK
  have hIK : ∀ x ∈ I ^ j, ∀ y ∈ I, x * y ∈ K := fun x hx y hy => by
    rw [hK, pow_succ]; exact Ideal.mul_mem_mul hx hy

  let w : PowerSeries T := PowerSeries.mk fun i => PowerSeries.coeff (M + i) s
  let r : PowerSeries T := s - PowerSeries.X ^ M * w
  have hr : ∀ i, PowerSeries.coeff i r ∈ I := by
    intro i
    show PowerSeries.coeff i (s - PowerSeries.X ^ M * w) ∈ I
    rw [map_sub, PowerSeries.coeff_X_pow_mul']
    by_cases hi : M ≤ i
    · rw [if_pos hi, PowerSeries.coeff_mk, Nat.add_sub_cancel' hi, sub_self]; exact I.zero_mem
    · rw [if_neg hi, sub_zero]; exact hsI i (not_le.mp hi)
  have hw0 : PowerSeries.constantCoeff w = PowerSeries.coeff M s := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, add_zero]
  let mkI := Ideal.Quotient.mk I
  have hmap : PowerSeries.map mkI s = PowerSeries.map mkI (PowerSeries.X ^ M * w) := by
    have h1 : PowerSeries.map mkI r = 0 := by
      ext i; rw [PowerSeries.coeff_map, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hr i)
    have hr' : s = r + PowerSeries.X ^ M * w := by show s = (s - PowerSeries.X ^ M * w) + _; ring
    rw [hr', map_add, h1, zero_add]
  have hcong : ∀ m n, PowerSeries.coeff n (s ^ m) - PowerSeries.coeff n ((PowerSeries.X ^ M * w) ^ m) ∈ I := by
    intro m n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have := congrArg (fun f => PowerSeries.coeff n f) (congrArg (fun f => f ^ m) hmap)
    simp only [← map_pow, PowerSeries.coeff_map] at this
    exact this

  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have h0 : (∑ᶠ m : ℕ, PowerSeries.coeff m d • PowerSeries.coeff (m₀ * M) (s ^ m)) ∈ K := by
    have := PowerSeries.coeff_subst hsub d (Finsupp.single () (m₀ * M))
    have h' : MvPowerSeries.coeff (Finsupp.single () (m₀ * M)) (PowerSeries.subst s d) ∈ K := hds (m₀ * M)
    rw [this] at h'
    exact h'

  have hsupp : (Function.support fun m : ℕ => PowerSeries.coeff m d • PowerSeries.coeff (m₀ * M) (s ^ m)) ⊆
      (Finset.range (m₀ * M + 1) : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    apply hm
    show PowerSeries.coeff m d • PowerSeries.coeff (m₀ * M) (s ^ m) = 0
    rw [coeff_pow_eq_zero_of_lt s hs0 (not_lt.mp hge |> fun h => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp] at h0

  let φ := Ideal.Quotient.mk K
  have hterm : ∀ m ∈ Finset.range (m₀ * M + 1), m ≠ m₀ →
      φ (PowerSeries.coeff m d • PowerSeries.coeff (m₀ * M) (s ^ m)) = 0 := by
    intro m _ hne
    rw [Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact K.mul_mem_right _ (hmin m hlt)
    · have h1 := hcong m (m₀ * M)
      rw [coeff_X_pow_mul_pow w M m m₀ hM, if_neg hne, if_neg (not_lt.mpr hgt.le), sub_zero] at h1
      exact hIK _ (hd m) _ h1
  have hmain : φ (PowerSeries.coeff m₀ d • PowerSeries.coeff (m₀ * M) (s ^ m₀)) =
      φ (PowerSeries.coeff m₀ d * PowerSeries.coeff M s ^ m₀) := by
    have h1 := hcong m₀ (m₀ * M)
    rw [coeff_X_pow_mul_pow w M m₀ m₀ hM, if_pos rfl, hw0] at h1
    rw [smul_eq_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← mul_sub]
    exact hIK _ (hd m₀) _ h1
  have hm₀mem : m₀ ∈ Finset.range (m₀ * M + 1) := by
    simp only [Finset.mem_range]
    calc m₀ = m₀ * 1 := (mul_one _).symm
      _ ≤ m₀ * M := Nat.mul_le_mul_left _ hM
      _ < m₀ * M + 1 := Nat.lt_succ_self _
  have hsum : φ (∑ m ∈ Finset.range (m₀ * M + 1), PowerSeries.coeff m d • PowerSeries.coeff (m₀ * M) (s ^ m)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h0
  rw [map_sum, Finset.sum_eq_single_of_mem m₀ hm₀mem (fun m hm hne => hterm m hm hne), hmain,
    Ideal.Quotient.eq_zero_iff_mem] at hsum
  exact hm₀ ((Ideal.mul_unit_mem_iff_mem K (hsM.pow m₀)).mp hsum)

theorem coeff_subst_mem {T : Type*} [CommRing T] (J : Ideal T) (a f : PowerSeries T)
    (ha : PowerSeries.constantCoeff a = 0) (hf : ∀ m, PowerSeries.coeff m f ∈ J) :
    ∀ m, PowerSeries.coeff m (PowerSeries.subst a f) ∈ J := by
  classical
  intro m
  have hsub : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have := PowerSeries.coeff_subst hsub f (Finsupp.single () m)
  rw [show PowerSeries.coeff m (PowerSeries.subst a f) = MvPowerSeries.coeff (Finsupp.single () m) (PowerSeries.subst a f)
    from rfl, this]
  have hsupp : (Function.support fun i : ℕ => PowerSeries.coeff i f • PowerSeries.coeff m (a ^ i)) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    apply hi
    show PowerSeries.coeff i f • PowerSeries.coeff m (a ^ i) = 0
    rw [coeff_pow_eq_zero_of_lt a ha (not_lt.mp hge |> fun h => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h),
      smul_zero]
  show (∑ᶠ i : ℕ, PowerSeries.coeff i f • PowerSeries.coeff m (a ^ i)) ∈ J
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  exact J.sum_mem fun i _ => by rw [smul_eq_mul]; exact J.mul_mem_right _ (hf i)

noncomputable def iter {T : Type*} [CommRing T] (s : PowerSeries T) : ℕ → PowerSeries T
  | 0 => PowerSeries.X
  | e + 1 => PowerSeries.subst s (iter s e)

theorem iter_zero {T : Type*} [CommRing T] (s : PowerSeries T) : iter s 0 = PowerSeries.X := rfl
theorem iter_succ {T : Type*} [CommRing T] (s : PowerSeries T) (e : ℕ) :
    iter s (e + 1) = PowerSeries.subst s (iter s e) := rfl

theorem constantCoeff_iter {T : Type*} [CommRing T] (s : PowerSeries T) (hs : PowerSeries.constantCoeff s = 0) :
    ∀ e, PowerSeries.constantCoeff (iter s e) = 0 := by
  intro e
  induction e with
  | zero => rw [iter_zero]; exact PowerSeries.constantCoeff_X
  | succ e ih =>
    rw [iter_succ]
    have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show PowerSeries.coeff 0 (PowerSeries.subst s (iter s e)) =
        MvPowerSeries.coeff (Finsupp.single () 0) (PowerSeries.subst s (iter s e)) from rfl,
      PowerSeries.coeff_subst hsub]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro i
    show PowerSeries.coeff i (iter s e) • PowerSeries.coeff 0 (s ^ i) = 0
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ih, zero_smul]
    · rw [coeff_pow_eq_zero_of_lt s hs hpos, smul_zero]

end R1aAux

namespace R1aAux

open PowerSeries

theorem subst_X_self {T : Type*} [CommRing T] (f : PowerSeries T) :
    PowerSeries.subst (PowerSeries.X : PowerSeries T) f = f := by
  show MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X () : MvPowerSeries Unit T)) f = f
  have : (fun _ : Unit => (MvPowerSeries.X () : MvPowerSeries Unit T)) = MvPowerSeries.X := by
    funext u; cases u; rfl
  rw [this, MvPowerSeries.subst_self]
  rfl

theorem map_toMv {T S : Type*} [CommRing T] [CommRing S] (f : T →+* S) (φ : PowerSeries T) :
    MvPowerSeries.map f (MvFormalGroup.toMv φ) = MvFormalGroup.toMv (PowerSeries.map f φ) := by
  rw [MvFormalGroup.toMv_def, MvFormalGroup.toMv_def]
  exact (MvPowerSeries.rename_map _ f φ).symm

theorem toMv_subst {T : Type*} [CommRing T] (a f : PowerSeries T) (ha : PowerSeries.constantCoeff a = 0) :
    MvFormalGroup.toMv (PowerSeries.subst a f) =
      MvPowerSeries.subst (fun _ : Fin 1 => MvFormalGroup.toMv a) (MvFormalGroup.toMv f) := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  rw [MvFormalGroup.toMv_def (PowerSeries.subst a f), show PowerSeries.subst a f = MvPowerSeries.subst (fun _ : Unit => a) f from rfl,
    MvFormalGroup.rename_subst MvFormalGroup.e1 h1, MvFormalGroup.toMv_def f,
    MvFormalGroup.subst_rename MvFormalGroup.e1 (MvFormalGroup.hasSubst_toMv ha)]
  rfl

theorem nthSeries_pow_eq_iter {T : Type*} [CommRing T] (G : FormalGroup T) [G.IsComm] (q e : ℕ) :
    G.nthSeries (q ^ e) = iter (G.nthSeries q) e := by
  classical
  haveI : (MvFormalGroup.ofFormalGroup G).IsComm := MvFormalGroup.instIsCommOfFormalGroup G
  have hs0 : PowerSeries.constantCoeff (G.nthSeries q) = 0 := FormalGroup.constantCoeff_nthSeries G q
  have hE : ∀ e, MvFormalGroup.Hom.toPowerSeries ((q ^ e : ℕ) : MvFormalGroup.End (MvFormalGroup.ofFormalGroup G)) =
      fun _ => MvFormalGroup.toMv (iter (G.nthSeries q) e) := by
    intro e
    induction e with
    | zero =>
      rw [pow_zero, Nat.cast_one, MvFormalGroup.End.toPowerSeries_one, iter_zero]
      funext i
      rw [MvFormalGroup.toMv_X, Subsingleton.elim i 0]
    | succ e ih =>
      rw [pow_succ, Nat.cast_mul, MvFormalGroup.End.toPowerSeries_mul, ih, MvFormalGroup.End.toPowerSeries_natCast,
        MvFormalGroup.nthSeries_ofFormalGroup, iter_succ]
      funext i
      exact (toMv_subst _ _ hs0).symm
  have h1 := hE e
  rw [MvFormalGroup.End.toPowerSeries_natCast, MvFormalGroup.nthSeries_ofFormalGroup] at h1
  exact MvFormalGroup.toMv_injective (congrFun h1 0)

theorem subst_iter_comm {T : Type*} [CommRing T] {G G' : FormalGroup T} (ψ : FormalGroup.LawHom G G') (q : ℕ) :
    ∀ e, PowerSeries.subst ψ.series (iter (G'.nthSeries q) e) = PowerSeries.subst (iter (G.nthSeries q) e) ψ.series := by
  have hs0 : PowerSeries.constantCoeff (G.nthSeries q) = 0 := FormalGroup.constantCoeff_nthSeries G q
  have hs'0 : PowerSeries.constantCoeff (G'.nthSeries q) = 0 := FormalGroup.constantCoeff_nthSeries G' q
  have hψ : PowerSeries.HasSubst ψ.series := PowerSeries.HasSubst.of_constantCoeff_zero ψ.constantCoeff_series
  have hS : PowerSeries.HasSubst (G.nthSeries q) := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hS' : PowerSeries.HasSubst (G'.nthSeries q) := PowerSeries.HasSubst.of_constantCoeff_zero hs'0
  intro e
  induction e with
  | zero => rw [iter_zero, iter_zero, PowerSeries.subst_X hψ, subst_X_self]
  | succ e ih =>
    have hI : PowerSeries.HasSubst (iter (G.nthSeries q) e) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_iter _ hs0 e)
    rw [iter_succ, iter_succ, PowerSeries.subst_comp_subst_apply hS' hψ,
      ← FormalGroup.LawHom.subst_nthSeries_series_eq ψ q, ← PowerSeries.subst_comp_subst_apply hψ hS, ih,
      PowerSeries.subst_comp_subst_apply hI hS]

end R1aAux

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] {T k : Type*} [CommRing T] [Field k] [CharP k q]
    (π : T →+* k) (hπs : Function.Surjective π) (n : ℕ) (hπ : RingHom.ker π ^ n = ⊥) (hqn : (q : T) ^ n = 0)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (G G' : FormalGroup T) [G'.IsComm] (hG : G.IsBaseChange π F₀) (hG' : G'.IsBaseChange π F₀)
    (ψ₁ ψ₂ : FormalGroup.LawHom G G')
    (h : PowerSeries.map π ψ₁.series = PowerSeries.map π ψ₂.series) :
    ψ₁.series = ψ₂.series := by
  classical

  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h10 : (1 : T) = 0 := by
      have h1 : (1 : T) ∈ RingHom.ker π ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; trivial
      rw [hπ] at h1
      exact (Ideal.mem_bot).mp h1
    haveI : Subsingleton T := subsingleton_of_zero_eq_one h10.symm
    exact Subsingleton.elim _ _
  set I : Ideal T := RingHom.ker π with hI
  set s : PowerSeries T := G.nthSeries q with hs
  set s' : PowerSeries T := G'.nthSeries q with hs'
  have hs0 : PowerSeries.constantCoeff s = 0 := FormalGroup.constantCoeff_nthSeries G q

  obtain ⟨u, hu, hqu⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀
  have hmaps : PowerSeries.map π s = u * PowerSeries.X ^ (q * q) := by
    rw [hs, ← hqu]; exact (FormalGroup.IsBaseChange.nthSeries_eq_map G π F₀ hG q).symm
  have hq1 : 0 < q := (Fact.out : q.Prime).pos
  have hM : 0 < q * q := Nat.mul_pos hq1 hq1
  have hsI : ∀ i < q * q, PowerSeries.coeff i s ∈ I := by
    intro i hi
    rw [hI, RingHom.mem_ker, ← PowerSeries.coeff_map, hmaps, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hi)]
  have hunit : ∀ x : T, IsUnit (π x) → IsUnit x := by
    intro x hx
    obtain ⟨t, ht⟩ := hπs ((hx.unit⁻¹ : kˣ) : k)
    have h1 : x * t - 1 ∈ I := by
      rw [hI, RingHom.mem_ker, map_sub, map_mul, ht, map_one, IsUnit.mul_val_inv, sub_self]
    have hnil : IsNilpotent (x * t - 1) := by
      refine ⟨n, ?_⟩
      have := Ideal.pow_mem_pow h1 n
      rw [hπ] at this
      exact (Ideal.mem_bot).mp this
    have h2 : IsUnit (x * t) := by have := hnil.isUnit_add_one; rwa [sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left h2
  have hsM : IsUnit (PowerSeries.coeff (q * q) s) := by
    apply hunit
    rw [← PowerSeries.coeff_map, hmaps, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.isUnit_iff_constantCoeff.mp hu

  set d : PowerSeries T := ψ₁.series - ψ₂.series with hd
  have hdI : ∀ m, PowerSeries.coeff m d ∈ I ^ 1 := by
    intro m
    rw [pow_one, hI, RingHom.mem_ker, hd, map_sub, map_sub, sub_eq_zero, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map, h]

  have stepA : PowerSeries.subst ψ₁.series (G'.nthSeries (q ^ (n * (n - 1)))) =
      PowerSeries.subst ψ₂.series (G'.nthSeries (q ^ (n * (n - 1)))) := by
    haveI : (MvFormalGroup.ofFormalGroup G').IsComm := MvFormalGroup.instIsCommOfFormalGroup G'

    let πI : T →+* T ⧸ I := Ideal.Quotient.mk I
    have hIμ : RingHom.ker πI ^ ((n - 1) + 1) = ⊥ := by
      rw [Nat.sub_add_cancel hnpos, show RingHom.ker πI = I from Ideal.mk_ker]; exact hπ
    have hmapI : PowerSeries.map πI ψ₁.series = PowerSeries.map πI ψ₂.series := by
      ext m
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      have := hdI m
      rwa [pow_one, hd, map_sub] at this
    obtain ⟨hpart, -⟩ := MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
      πI (n - 1) hIμ q n hqn (MvFormalGroup.ofFormalGroup G')
    have key := hpart (Fin 1) (fun _ => MvFormalGroup.toMv ψ₁.series) (fun _ => MvFormalGroup.toMv ψ₂.series)
      (fun _ => by rw [MvFormalGroup.constantCoeff_toMv]; exact ψ₁.constantCoeff_series)
      (fun _ => by rw [MvFormalGroup.constantCoeff_toMv]; exact ψ₂.constantCoeff_series)
      (fun _ => by rw [R1aAux.map_toMv, R1aAux.map_toMv, hmapI]) 0
    rw [MvFormalGroup.nthSeries_ofFormalGroup] at key
    rw [← R1aAux.toMv_subst _ _ ψ₁.constantCoeff_series, ← R1aAux.toMv_subst _ _ ψ₂.constantCoeff_series] at key
    exact MvFormalGroup.toMv_injective key

  generalize he₀ : n * (n - 1) = e₀ at stepA
  have hcomp : PowerSeries.subst (R1aAux.iter s e₀) d = 0 := by
    have hI0 : PowerSeries.HasSubst (R1aAux.iter s e₀) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (R1aAux.constantCoeff_iter _ hs0 e₀)
    rw [hd, PowerSeries.subst_sub hI0, hs, ← R1aAux.subst_iter_comm ψ₁ q e₀, ← R1aAux.subst_iter_comm ψ₂ q e₀,
      ← R1aAux.nthSeries_pow_eq_iter G' q e₀, stepA, sub_self]

  have hP : ∀ j, 1 ≤ j → ∀ m, PowerSeries.coeff m d ∈ I ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hdI
    | succ j _ ih =>

      have hQ : ∀ t, t ≤ e₀ → ∀ m, PowerSeries.coeff m (PowerSeries.subst (R1aAux.iter s (e₀ - t)) d) ∈ I ^ (j + 1) := by
        intro t
        induction t with
        | zero => intro _ m; rw [Nat.sub_zero, hcomp, map_zero]; exact Submodule.zero_mem _
        | succ t iht =>
          intro ht m
          have hlt : e₀ - (t + 1) + 1 = e₀ - t := by omega
          have hprev := iht (Nat.le_of_succ_le ht)

          have hI1 : PowerSeries.HasSubst (R1aAux.iter s (e₀ - (t + 1))) :=
            PowerSeries.HasSubst.of_constantCoeff_zero (R1aAux.constantCoeff_iter _ hs0 _)
          have hS : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs0
          refine R1aAux.cancel I s (PowerSeries.subst (R1aAux.iter s (e₀ - (t + 1))) d) (q * q) j hM hs0 hsI hsM
            (R1aAux.coeff_subst_mem (I ^ j) _ d (R1aAux.constantCoeff_iter _ hs0 _) ih) ?_ m
          intro m'
          rw [PowerSeries.subst_comp_subst_apply hI1 hS, ← R1aAux.iter_succ, hlt]
          exact hprev m'
      have := hQ e₀ le_rfl
      rw [Nat.sub_self, R1aAux.iter_zero] at this
      intro m
      have h1 := this m
      rwa [R1aAux.subst_X_self] at h1

  have hd0 : d = 0 := by
    ext m
    have := hP n hnpos m
    rw [hπ] at this
    rw [map_zero]
    exact (Ideal.mem_bot).mp this
  exact sub_eq_zero.mp hd0

#print axioms solution

end S_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot (solution)
