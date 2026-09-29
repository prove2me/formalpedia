-- Prove2me | solution 1 for CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/694a70bc-b8a9-5aa5-8a6f-beade8e6cdcd

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CerednikDrinfeld CerednikDrinfeld.Omega

namespace P2mKcGlobalDiv

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "Ω" => upperHalfPlane K₀ K

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem mem_affinoid_of_v_sub_lt {n : ℕ} {w₀ : K} (hw₀ : w₀ ∈ affinoid ϖ n) {ζ : K}
    (hζ : Valued.v (ζ - w₀) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n) : ζ ∈ affinoid ϖ n := by
  obtain ⟨h1, h2⟩ := (mem_affinoid_iff' ϖ n w₀).1 hw₀
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' ϖ.lt_one.le
  have hP1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
    one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le)
  rw [mem_affinoid_iff']
  refine ⟨?_, fun a => ?_⟩
  · rw [show ζ = (ζ - w₀) + w₀ by ring]
    exact (Valuation.map_add _ _ _).trans (max_le (hζ.le.trans (hp1.trans hP1)) h1)
  · have hlt : Valued.v (ζ - w₀) < Valued.v (w₀ - algebraMap K₀ K a) := hζ.trans_le (h2 a)
    rw [show ζ - algebraMap K₀ K a = (ζ - w₀) + (w₀ - algebraMap K₀ K a) by ring,
      Valuation.map_add_eq_of_lt_right _ hlt]
    exact h2 a

theorem isHolOn_comp_inclusion {S S' : Set K} (hSS' : S ⊆ S') {f : ↥S' → K} (hf : IsHolOn K S' f) :
    IsHolOn K S (f ∘ Set.inclusion hSS') := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hSS' hz), ⟨b, fun k z => hb k (Set.inclusion hSS' z)⟩, ?_⟩
  rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
  intro γ
  filter_upwards [hlim γ] with k hk z
  exact hk (Set.inclusion hSS' z)

def resLevel {m n : ℕ} (h : m ≤ n) (Q : ↥(affinoid ϖ n) → K) : ↥(affinoid ϖ m) → K :=
  Q ∘ Set.inclusion (affinoid_mono ϖ h)

theorem resLevel_mem_holOn {m n : ℕ} (h : m ≤ n) {Q : ↥(affinoid ϖ n) → K} (hQ : Q ∈ holOn K (affinoid ϖ n)) :
    resLevel ϖ h Q ∈ holOn K (affinoid ϖ m) :=
  isHolOn_comp_inclusion (affinoid_mono ϖ h) hQ

@[scoped simp] theorem resLevel_apply {m n : ℕ} (h : m ≤ n) (Q : ↥(affinoid ϖ n) → K) (w : ↥(affinoid ϖ m)) :
    resLevel ϖ h Q w = Q ⟨w, affinoid_mono ϖ h w.2⟩ := rfl

@[scoped simp] theorem restrictAffinoid_apply' (n : ℕ) (f : ↥Ω → K) (w : ↥(affinoid ϖ n)) :
    restrictAffinoid ϖ n f w = f ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ := rfl

theorem apply_eq_zero_of_coordSub_dvd {F : ↥(holRing ϖ)} {z : ↥Ω} (h : coordSub ϖ z ∣ F) :
    (F : ↥Ω → K) z = 0 := by
  obtain ⟨G, rfl⟩ := h
  show ((coordSub ϖ z : ↥(holRing ϖ)) : ↥Ω → K) z * (G : ↥Ω → K) z = 0
  rw [coordSub_apply_self, zero_mul]

theorem ordAt_eq_zero_of_apply_ne_zero {F : ↥(holRing ϖ)} {z : ↥Ω} (h : (F : ↥Ω → K) z ≠ 0) :
    ordAt ϖ F z = 0 := by
  apply Nat.le_zero.1
  refine ordAt_le_of_forall_le ϖ F z 0 fun n hn => ?_
  by_contra hn0
  exact h (apply_eq_zero_of_coordSub_dvd ϖ ((dvd_pow_self _ (by omega)).trans hn))

theorem coe_mul_apply (F G : ↥(holRing ϖ)) (z : ↥Ω) :
    ((F * G : ↥(holRing ϖ)) : ↥Ω → K) z = (F : ↥Ω → K) z * (G : ↥Ω → K) z := rfl

theorem coe_pow_apply (F : ↥(holRing ϖ)) (n : ℕ) (z : ↥Ω) :
    ((F ^ n : ↥(holRing ϖ)) : ↥Ω → K) z = (F : ↥Ω → K) z ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coe_mul_apply, ih, pow_succ]

variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
  Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)

include hrk hex hlf in
theorem pow_ordAt_dvd {F : ↥(holRing ϖ)} (hF : F ≠ 0) (z : ↥Ω) : coordSub ϖ z ^ ordAt ϖ F z ∣ F := by
  classical
  exact Nat.sSup_mem ⟨0, zero_mem_setOf_pow_dvd ϖ F z⟩
    (CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hlf F hF z)

include hrk hex hlf in

theorem restrictAffinoid_ne_zero {F : ↥(holRing ϖ)} (hF : F ≠ 0) (n : ℕ) (hne : (affinoid ϖ n).Nonempty) :
    restrictAffinoid ϖ n (F : ↥Ω → K) ≠ 0 := by
  intro h0
  obtain ⟨w₀, hw₀⟩ := hne
  apply hF
  apply Subtype.ext
  funext z
  obtain ⟨m, hm⟩ := hex (z : K) z.2
  set k := max m n with hk
  have hzk : (z : K) ∈ affinoid ϖ k := affinoid_mono ϖ (le_max_left m n) hm
  have hw₀k : w₀ ∈ affinoid ϖ k := affinoid_mono ϖ (le_max_right m n) hw₀
  have hg : restrictAffinoid ϖ k (F : ↥Ω → K) ∈ holOn K (affinoid ϖ k) := F.2 k
  have hc : (algebraMap K₀ K ϖ.ϖ) ^ n ≠ 0 := pow_ne_zero n (algebraMap_varpi_ne_zero ϖ)
  have hzero := CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk k
    (hlf k) hg hw₀k hc (fun ζ hζ => by
      rw [Valuation.map_pow] at hζ
      have hζn : (ζ : K) ∈ affinoid ϖ n := mem_affinoid_of_v_sub_lt ϖ hw₀ hζ
      have := congrArg (fun g : ↥(affinoid ϖ n) → K => g ⟨ζ, hζn⟩) h0
      simpa [restrictAffinoid] using this)
  have := congrArg (fun g : ↥(affinoid ϖ k) → K => g ⟨z, hzk⟩) hzero
  simpa [restrictAffinoid] using this

include hrk hex hlf in

theorem exists_peel (F G : ↥(holRing ϖ)) (hF : F ≠ 0) (hG : G ≠ 0)
    (h : ∀ z : ↥Ω, ordAt ϖ G z ≤ ordAt ϖ F z) (S : Finset ↥Ω) :
    ∃ P U F₁ : ↥(holRing ϖ), G = P * U ∧ F = P * F₁ ∧ (∀ z ∈ S, (U : ↥Ω → K) z ≠ 0) ∧
      (∀ z : ↥Ω, z ∉ S → (P : ↥Ω → K) z ≠ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, G, F, (one_mul G).symm, (one_mul F).symm, fun z hz => absurd hz (by simp), fun z _ => by simp⟩
  | @insert z₀ S hz₀ ih =>
    obtain ⟨P, U, F₁, hGP, hFP, hUS, hPS⟩ := ih
    have hP0 : P ≠ 0 := by rintro rfl; exact hG (by rw [hGP, zero_mul])
    have hU0 : U ≠ 0 := by rintro rfl; exact hG (by rw [hGP, mul_zero])
    have hF₁0 : F₁ ≠ 0 := by rintro rfl; exact hF (by rw [hFP, mul_zero])
    have hPz₀ : ordAt ϖ P z₀ = 0 := ordAt_eq_zero_of_apply_ne_zero ϖ (hPS z₀ hz₀)

    have hGo : ordAt ϖ G z₀ = ordAt ϖ U z₀ := by
      rw [hGP, CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hlf P U hP0 hU0 z₀, hPz₀, zero_add]
    have hFo : ordAt ϖ F z₀ = ordAt ϖ F₁ z₀ := by
      rw [hFP, CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hlf P F₁ hP0 hF₁0 z₀, hPz₀, zero_add]
    set m := ordAt ϖ U z₀ with hm

    obtain ⟨U', hU', hU'z⟩ :=
      CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf U hU0 z₀
    rw [← hm] at hU'
    have hmF : m ≤ ordAt ϖ F₁ z₀ := by rw [← hFo, ← hGo]; exact h z₀
    obtain ⟨F₁', hF₁'⟩ : coordSub ϖ z₀ ^ m ∣ F₁ :=
      (pow_dvd_pow _ hmF).trans (pow_ordAt_dvd ϖ hrk hex hlf hF₁0 z₀)
    refine ⟨P * coordSub ϖ z₀ ^ m, U', F₁', ?_, ?_, ?_, ?_⟩
    · rw [hGP, hU', mul_assoc]
    · rw [hFP, hF₁', mul_assoc]
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hU'z
      · intro hz0
        apply hUS z hz
        rw [hU', coe_mul_apply, hz0, mul_zero]
    · intro z hz hPz
      rw [Finset.mem_insert, not_or] at hz
      rw [coe_mul_apply, coe_pow_apply, coordSub_apply] at hPz
      rcases mul_eq_zero.1 hPz with h1 | h2
      · exact hPS z hz.2 h1
      · have := pow_eq_zero_iff'.1 h2
        exact hz.1 (Subtype.ext (sub_eq_zero.1 this.1))

include hrk hex hlf in

theorem exists_local_quotient (F G : ↥(holRing ϖ)) (hF : F ≠ 0) (hG : G ≠ 0)
    (h : ∀ z : ↥Ω, ordAt ϖ G z ≤ ordAt ϖ F z) (n : ℕ) :
    ∃ Q : ↥(affinoid ϖ n) → K, Q ∈ holOn K (affinoid ϖ n) ∧
      ∀ w : ↥(affinoid ϖ n), (G : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ * Q w =
        (F : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ := by
  classical

  have hZ : {w : ↥(affinoid ϖ n) | restrictAffinoid ϖ n (G : ↥Ω → K) w = 0}.Finite := by
    by_cases hne : (affinoid ϖ n).Nonempty
    · exact CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid K₀ K ϖ hrk n (hlf n) (G.2 n)
        (restrictAffinoid_ne_zero ϖ hrk hex hlf hG n hne)
    · haveI : IsEmpty ↥(affinoid ϖ n) := ⟨fun w => hne ⟨w, w.2⟩⟩
      exact Set.toFinite _
  let incl : ↥(affinoid ϖ n) → ↥Ω := Set.inclusion (affinoid_subset_upperHalfPlane ϖ n)
  obtain ⟨P, U, F₁, hGP, hFP, hUS, -⟩ := exists_peel ϖ hrk hex hlf F G hF hG h (hZ.toFinset.image incl)

  have hU : ∀ w : ↥(affinoid ϖ n), (U : ↥Ω → K) (incl w) ≠ 0 := fun w hw => by
    have hGw : (G : ↥Ω → K) (incl w) = 0 := by rw [hGP, coe_mul_apply, hw, mul_zero]
    have hmem : incl w ∈ hZ.toFinset.image incl :=
      Finset.mem_image.2 ⟨w, hZ.mem_toFinset.2 (by simpa [restrictAffinoid] using hGw), rfl⟩
    exact hUS _ hmem hw

  obtain ⟨W, hW, hUW⟩ :=
    CerednikDrinfeld.Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero K₀ K ϖ hrk n (hlf n) (U.2 n)
      (fun w => hU w)
  refine ⟨restrictAffinoid ϖ n (F₁ : ↥Ω → K) * W, Subring.mul_mem _ (F₁.2 n) hW, fun w => ?_⟩
  have hUWw : (U : ↥Ω → K) (incl w) * W w = 1 := by
    have := congrArg (fun g : ↥(affinoid ϖ n) → K => g w) hUW
    simpa [restrictAffinoid] using this
  show (G : ↥Ω → K) (incl w) * ((F₁ : ↥Ω → K) (incl w) * W w) = (F : ↥Ω → K) (incl w)
  rw [hGP, hFP, coe_mul_apply, coe_mul_apply]
  calc (P : ↥Ω → K) (incl w) * (U : ↥Ω → K) (incl w) * ((F₁ : ↥Ω → K) (incl w) * W w)
      = (P : ↥Ω → K) (incl w) * (F₁ : ↥Ω → K) (incl w) * ((U : ↥Ω → K) (incl w) * W w) := by ring
    _ = (P : ↥Ω → K) (incl w) * (F₁ : ↥Ω → K) (incl w) := by rw [hUWw, mul_one]

include hrk hlf hex in

theorem local_quotient_unique {G : ↥(holRing ϖ)} (hG : G ≠ 0) (n : ℕ) {Q Q' : ↥(affinoid ϖ n) → K}
    (hQ : Q ∈ holOn K (affinoid ϖ n)) (hQ' : Q' ∈ holOn K (affinoid ϖ n))
    (hqq : ∀ w : ↥(affinoid ϖ n), (G : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ * Q w =
      (G : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ * Q' w) :
    Q = Q' := by
  by_cases hne : (affinoid ϖ n).Nonempty
  swap
  · funext w; exact absurd ⟨(w : K), w.2⟩ hne

  have hGn := restrictAffinoid_ne_zero ϖ hrk hex hlf hG n hne
  obtain ⟨w₁, hw₁⟩ := Function.ne_iff.1 hGn
  obtain ⟨c, hc, hdisc⟩ :=
    CerednikDrinfeld.Omega.exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn K (G.2 n) w₁ hw₁

  have hD : Q - Q' ∈ holOn K (affinoid ϖ n) := Subring.sub_mem _ hQ hQ'
  have h0 : ∀ w : ↥(affinoid ϖ n), Valued.v ((w : K) - (w₁ : K)) < Valued.v c → (Q - Q') w = 0 := fun w hw => by
    have hGw : restrictAffinoid ϖ n (G : ↥Ω → K) w ≠ 0 := hdisc w hw
    have := hqq w
    rw [Pi.sub_apply, sub_eq_zero]
    exact mul_left_cancel₀ hGw this
  have := CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk n (hlf n) hD
    w₁.2 hc h0
  exact sub_eq_zero.1 this

include hrk hlf hex in

theorem dvd_of_local_quotients {F G : ↥(holRing ϖ)} (hG : G ≠ 0)
    (hloc : ∀ n : ℕ, ∃ Q : ↥(affinoid ϖ n) → K, Q ∈ holOn K (affinoid ϖ n) ∧
      ∀ w : ↥(affinoid ϖ n), (G : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ * Q w =
        (F : ↥Ω → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩) :
    G ∣ F := by
  classical
  choose Qf hQf hQeq using hloc

  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n) (w : ↥(affinoid ϖ m)),
      Qf n ⟨w, affinoid_mono ϖ hmn w.2⟩ = Qf m w := fun {m n} hmn w => by
    have heq : resLevel ϖ hmn (Qf n) = Qf m := by
      refine local_quotient_unique ϖ hrk hex hlf hG m (resLevel_mem_holOn ϖ hmn (hQf n)) (hQf m) fun w' => ?_
      rw [resLevel_apply, hQeq m w']
      exact hQeq n ⟨w', affinoid_mono ϖ hmn w'.2⟩
    have := congrArg (fun g => g w) heq
    simpa using this

  have hexz : ∀ z : ↥Ω, ∃ n, (z : K) ∈ affinoid ϖ n := fun z => hex (z : K) z.2
  let Q : ↥Ω → K := fun z => Qf (Nat.find (hexz z)) ⟨z, Nat.find_spec (hexz z)⟩
  have hQres : ∀ n : ℕ, restrictAffinoid ϖ n Q = Qf n := fun n => by
    funext w
    rw [restrictAffinoid_apply']
    set z : ↥Ω := ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ with hz
    have hmin : Nat.find (hexz z) ≤ n := Nat.find_min' (hexz z) w.2
    show Qf (Nat.find (hexz z)) ⟨z, Nat.find_spec (hexz z)⟩ = Qf n w
    have := hcompat hmin ⟨(z : K), Nat.find_spec (hexz z)⟩
    exact this.symm
  have hQhol : Q ∈ holRing ϖ := fun n => by
    rw [hQres n]; exact hQf n
  refine ⟨⟨Q, hQhol⟩, Subtype.ext (funext fun z => ?_)⟩
  obtain ⟨n, hn⟩ := hexz z
  have h1 := hQeq n ⟨z, hn⟩
  rw [← hQres n, restrictAffinoid_apply'] at h1
  rw [coe_mul_apply]
  exact h1.symm

end P2mKcGlobalDiv
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le.P2mKcGlobalDiv"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le.P2mKcGlobalDiv"

open CerednikDrinfeld CerednikDrinfeld.Omega P2mKcGlobalDiv in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hG : G ≠ 0)
    (h : ∀ z : ↥(upperHalfPlane K₀ K), ordAt ϖ G z ≤ ordAt ϖ F z) :
    G ∣ F := by
  classical
  by_cases hF : F = 0
  · exact ⟨0, by rw [hF, mul_zero]⟩
  exact dvd_of_local_quotients ϖ hrk hex hfin hG (exists_local_quotient ϖ hrk hex hfin F G hF hG h)

end S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le (solution)
