-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/08169a99-7f7b-565d-b302-b1bf1a096951

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane RatPair RatPair.evalAt_pullback RatPair.isPoleFreeOn_pullback tendstoUniformly_iff_vRestrict IsHolOn IsHolOn.const holOn moebius pmoebius pmoebius_mk upperHalfPlane moebius_denom_ne_zero_of_mem coord_mem_holRing"
namespace TransportAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem isHolOn_restrict {S S' : Set K} (hS : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (fun w : ↥S' => f ⟨(w : K), hS w.2⟩) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hS hz), ⟨b, fun k w => hb k ⟨(w : K), hS w.2⟩⟩, ?_⟩
  exact hlim.comp (fun w : ↥S' => (⟨(w : K), hS w.2⟩ : ↥S))

theorem mem_affinoid_of_v_sub_le (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n)
    {w : K} (hw : Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) : w ∈ affinoid ϖ n := by
  obtain ⟨hz1, hz2⟩ := hz
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  have hlt : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ hp0 hp1 (Nat.lt_succ_self n)
  have hle1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≤ 1 := pow_le_one₀ zero_le' hp1.le
  have hge1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le)
  refine ⟨?_, fun a ha => ?_⟩
  · have : w = (w - z) + z := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (hw.trans (hle1.trans hge1)) hz1)
  · have hza := hz2 a ha
    have hlt' : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K a) := lt_of_le_of_lt hw (lt_of_lt_of_le hlt hza)
    have : w - algebraMap K₀ K a = (z - algebraMap K₀ K a) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt']
    exact hza

theorem coordFn_mem_holOn (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {S : Set K} (hS : S ⊆ affinoid ϖ n) :
    (fun z : ↥S => (z : K)) ∈ holOn K S :=
  isHolOn_restrict hS ((coord_mem_holRing ϖ) n)

theorem isHolOn_comp_moebius (g : GL (Fin 2) K₀) {S S' : Set K} (hS' : S' ⊆ upperHalfPlane K₀ K)
    (hmaps : Set.MapsTo (moebius K₀ K g) S' S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (fun z : ↥S' => f ⟨moebius K₀ K g (z : K), hmaps z.2⟩) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨fun k => (r k).pullback g, fun k => RatPair.isPoleFreeOn_pullback hS' g hmaps (r k) (hr k),
    ⟨b, fun k z => ?_⟩, ?_⟩
  · rw [RatPair.evalAt_pullback (hS' z.2)]
    exact hb k ⟨_, hmaps z.2⟩
  · rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
    intro δ
    filter_upwards [hlim δ] with k hk z
    have hz' := hk ⟨_, hmaps z.2⟩
    rw [RatPair.evalAt_pullback (hS' z.2)]
    exact hz'

end CerednikDrinfeld.Omega.TransportAux

open CerednikDrinfeld.Omega.TransportAux in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (F : ↥(upperHalfPlane K₀ K) → K)
    (hinv : ∀ (γ : G) (z w : ↥(upperHalfPlane K₀ K)), (w : K) = pmoebius K₀ (ρ γ) (z : K) → F w = F z)
    (γ : G) (m n : ℕ) (p : ↥(upperHalfPlane K₀ K)) (hp : (p : K) ∈ affinoid ϖ m)
    (s : K) (hs : s ≠ 0)
    (hE : ∀ w : K, Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s → w ∈ affinoid ϖ n)
    {φ : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s} → K}
    (hφ : φ ∈ holOn K {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s}) (e : ℕ)
    (he : e = 0 ∨ φ ⟨pmoebius K₀ (ρ γ) (p : K), by simp⟩ ≠ 0)
    (h : ∀ w : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s},
      (w : K) ≠ pmoebius K₀ (ρ γ) (p : K) →
      ((w : K) - pmoebius K₀ (ρ γ) (p : K)) ^ e *
          F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n (hE (w : K) w.2)⟩ = φ w) :
    ∃ r : K, r ≠ 0 ∧ ∃ hD : (∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ affinoid ϖ m),
      ∃ φ' : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r} → K,
        φ' ∈ holOn K {z : K | Valued.v (z - (p : K)) ≤ Valued.v r} ∧
        (e = 0 ∨ φ' ⟨(p : K), by simp⟩ ≠ 0) ∧
        ∀ z : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r}, (z : K) ≠ (p : K) →
          ((z : K) - (p : K)) ^ e *
              F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ m (hD (z : K) z.2)⟩ = φ' z := by
  classical
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  have hΩp : (p : K) ∈ upperHalfPlane K₀ K := p.2

  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk M = ρ γ := by
    generalize ρ γ = g
    induction g using Matrix.ProjGenLinGroup.induction_on with
    | _ g => exact ⟨g, rfl⟩
  set a : K := algebraMap K₀ K (M 0 0) with ha
  set b : K := algebraMap K₀ K (M 0 1) with hb
  set c : K := algebraMap K₀ K (M 1 0) with hc
  set d : K := algebraMap K₀ K (M 1 1) with hd
  have hden : ∀ z : K, z ∈ upperHalfPlane K₀ K → c * z + d ≠ 0 := fun z hz =>
    moebius_denom_ne_zero_of_mem K₀ hz M
  have hdet : a * d - b * c ≠ 0 := by
    have h1 : (M : Matrix (Fin 2) (Fin 2) K₀).det ≠ 0 := M.det_ne_zero
    rw [Matrix.det_fin_two] at h1
    intro h0
    apply h1
    apply (algebraMap K₀ K).injective
    rw [map_zero, map_sub, map_mul, map_mul]
    show a * d - b * c = 0
    exact h0
  have hpm : ∀ z : K, z ∈ upperHalfPlane K₀ K → pmoebius K₀ (ρ γ) z = (a * z + b) / (c * z + d) := by
    intro z hz
    rw [← hM, pmoebius_mk K₀ M z (hden z hz)]
    rfl
  have hmoeb : ∀ z : K, z ∈ upperHalfPlane K₀ K → moebius K₀ K M z = pmoebius K₀ (ρ γ) z := by
    intro z hz; rw [hpm z hz]; rfl
  set dp : K := c * (p : K) + d with hdp
  have hdp0 : dp ≠ 0 := hden _ hΩp
  have hdiff : ∀ z : K, z ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ γ) z - pmoebius K₀ (ρ γ) (p : K) = (a * d - b * c) * (z - (p : K)) / ((c * z + d) * dp) := by
    intro z hz
    rw [hpm z hz, hpm _ hΩp, hdp, div_sub_div _ _ (hden z hz) (hden _ hΩp)]
    congr 1
    ring

  set r₁ : K := (algebraMap K₀ K ϖ.ϖ) ^ (m + 1) with hr₁
  set r₂ : K := if c = 0 then r₁ else (algebraMap K₀ K ϖ.ϖ) * dp / c with hr₂
  set r₃ : K := s * dp ^ 2 / (a * d - b * c) with hr₃
  have hϖ0 : (algebraMap K₀ K ϖ.ϖ) ≠ 0 := by
    intro h0; have := congrArg Valued.v h0; rw [map_zero] at this; exact hp0.ne' this
  have hr₁0 : r₁ ≠ 0 := pow_ne_zero _ hϖ0
  have hr₂0 : r₂ ≠ 0 := by
    rw [hr₂]; split_ifs with hc0
    · exact hr₁0
    · exact div_ne_zero (mul_ne_zero hϖ0 hdp0) hc0
  have hr₃0 : r₃ ≠ 0 := div_ne_zero (mul_ne_zero hs (pow_ne_zero _ hdp0)) hdet
  have key : ∀ x y : K, x ≠ 0 → y ≠ 0 → ∃ t : K, t ≠ 0 ∧ Valued.v t ≤ Valued.v x ∧ Valued.v t ≤ Valued.v y := by
    intro x y hx hy
    rcases le_total (Valued.v x) (Valued.v y) with h | h
    · exact ⟨x, hx, le_rfl, h⟩
    · exact ⟨y, hy, h, le_rfl⟩
  obtain ⟨t, ht0, ht1, ht2⟩ := key r₁ r₂ hr₁0 hr₂0
  obtain ⟨r, hr0, hrt, hr3⟩ := key t r₃ ht0 hr₃0
  have hrle1 : Valued.v r ≤ Valued.v r₁ := hrt.trans ht1
  have hrle2 : Valued.v r ≤ Valued.v r₂ := hrt.trans ht2

  have hD : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ affinoid ϖ m := by
    intro z hz
    exact mem_affinoid_of_v_sub_le ϖ m hp (hz.trans (by rw [hr₁, map_pow] at hrle1; exact hrle1))
  have hDΩ : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ upperHalfPlane K₀ K :=
    fun z hz => affinoid_subset_upperHalfPlane ϖ m (hD z hz)

  have hcz : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → Valued.v (c * z + d) = Valued.v dp := by
    intro z hz
    have hlt : Valued.v (c * (z - (p : K))) < Valued.v dp := by
      by_cases hc0 : c = 0
      · rw [hc0, zero_mul, map_zero]; exact lt_of_le_of_ne zero_le' (fun h => hdp0 (by rwa [eq_comm, map_eq_zero] at h))
      · have h2 : Valued.v r ≤ Valued.v ((algebraMap K₀ K ϖ.ϖ) * dp / c) := by
          rw [hr₂, if_neg hc0] at hrle2; exact hrle2
        have hvc : 0 < Valued.v c := lt_of_le_of_ne zero_le' (fun h => hc0 (by rwa [eq_comm, map_eq_zero] at h))
        rw [map_mul]
        calc Valued.v c * Valued.v (z - (p : K)) ≤ Valued.v c * Valued.v ((algebraMap K₀ K ϖ.ϖ) * dp / c) :=
              mul_le_mul_right (hz.trans h2) _
          _ = Valued.v (algebraMap K₀ K ϖ.ϖ) * Valued.v dp := by
              rw [map_div₀, map_mul, mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hvc.ne', mul_one]
          _ < 1 * Valued.v dp := mul_lt_mul_of_pos_right hp1
              (lt_of_le_of_ne zero_le' (fun h => hdp0 (by rwa [eq_comm, map_eq_zero] at h)))
          _ = Valued.v dp := one_mul _
    have : c * z + d = dp + c * (z - (p : K)) := by rw [hdp]; ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt]
  have hcz0 : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → c * z + d ≠ 0 := by
    intro z hz h0
    have := hcz z hz
    rw [h0, map_zero, eq_comm, map_eq_zero] at this
    exact hdp0 this

  have hTE : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r →
      Valued.v (pmoebius K₀ (ρ γ) z - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s := by
    intro z hz
    rw [hdiff z (hDΩ z hz), map_div₀, map_mul, map_mul, hcz z hz]
    have hvdp : 0 < Valued.v dp := lt_of_le_of_ne zero_le' (fun h => hdp0 (by rwa [eq_comm, map_eq_zero] at h))
    rw [div_le_iff₀ (mul_pos hvdp hvdp)]
    have h3 : Valued.v (z - (p : K)) ≤ Valued.v (s * dp ^ 2 / (a * d - b * c)) := hz.trans hr3
    have hvdet : 0 < Valued.v (a * d - b * c) := lt_of_le_of_ne zero_le' (fun h => hdet (by rwa [eq_comm, map_eq_zero] at h))
    rw [map_div₀, le_div_iff₀ hvdet, map_mul, map_pow] at h3
    calc Valued.v (a * d - b * c) * Valued.v (z - (p : K)) = Valued.v (z - (p : K)) * Valued.v (a * d - b * c) := mul_comm _ _
      _ ≤ Valued.v s * Valued.v dp ^ 2 := h3
      _ = Valued.v s * (Valued.v dp * Valued.v dp) := by rw [sq]

  set Cinv : K → K := fun z => (c * z + d) * dp / (a * d - b * c) with hCinv
  have hCinv0 : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → Cinv z ≠ 0 := fun z hz =>
    div_ne_zero (mul_ne_zero (hcz0 z hz) hdp0) hdet
  have hdiff' : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r →
      (pmoebius K₀ (ρ γ) z - pmoebius K₀ (ρ γ) (p : K)) * Cinv z = z - (p : K) := by
    intro z hz
    rw [hdiff z (hDΩ z hz), hCinv]
    field_simp [hcz0 z hz, hdp0, hdet]
  set D : Set K := {z : K | Valued.v (z - (p : K)) ≤ Valued.v r} with hDdef
  have hmapsP : ∀ z : K, z ∈ D → pmoebius K₀ (ρ γ) z ∈ {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s} := fun z hz => hTE z hz
  have hmapsM : Set.MapsTo (moebius K₀ K M) D {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s} := fun z hz => by
    show moebius K₀ K M z ∈ {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s}
    rw [hmoeb z (hDΩ z hz)]; exact hmapsP z hz
  refine ⟨r, hr0, hD, fun z => φ ⟨pmoebius K₀ (ρ γ) (z : K), hmapsP (z : K) z.2⟩ * Cinv (z : K) ^ e, ?_, ?_, ?_⟩
  ·
    refine mul_mem ?_ ?_
    · have h1 : IsHolOn K D (fun z : ↥D => φ ⟨moebius K₀ K M (z : K), hmapsM z.2⟩) :=
        isHolOn_comp_moebius M (fun z hz => hDΩ z hz) hmapsM hφ
      have h2 : (fun z : ↥D => φ ⟨pmoebius K₀ (ρ γ) (z : K), hmapsP (z : K) z.2⟩) =
          (fun z : ↥D => φ ⟨moebius K₀ K M (z : K), hmapsM z.2⟩) := by
        funext z
        congr 1
        exact Subtype.ext (hmoeb (z : K) (hDΩ (z : K) z.2)).symm
      rw [h2]; exact h1
    · have hDm : D ⊆ affinoid ϖ m := fun z hz => hD z hz
      have : (fun z : ↥D => Cinv (z : K) ^ e) =
          ((((fun _ => c) * fun z : ↥D => (z : K)) + fun _ => d) * fun _ => dp / (a * d - b * c)) ^ e := by
        funext z; simp only [hCinv, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]; ring
      rw [this]
      exact pow_mem (mul_mem (add_mem (mul_mem (IsHolOn.const D c) (coordFn_mem_holOn ϖ m hDm))
        (IsHolOn.const D d)) (IsHolOn.const D _)) e
  ·
    rcases he with he0 | hne
    · exact Or.inl he0
    · right
      refine mul_ne_zero ?_ (pow_ne_zero _ (hCinv0 (p : K) (by simp)))
      exact hne
  ·
    intro z hzp
    have hzΩ : (z : K) ∈ upperHalfPlane K₀ K := hDΩ (z : K) z.2
    have hwq : pmoebius K₀ (ρ γ) (z : K) ≠ pmoebius K₀ (ρ γ) (p : K) := by
      intro h0
      have := hdiff' (z : K) z.2
      rw [h0, sub_self, zero_mul] at this
      exact hzp (sub_eq_zero.1 this.symm)
    have h1 := h ⟨pmoebius K₀ (ρ γ) (z : K), hmapsP (z : K) z.2⟩ hwq
    have hinv' : F ⟨pmoebius K₀ (ρ γ) (z : K), affinoid_subset_upperHalfPlane ϖ n (hE _ (hmapsP (z : K) z.2))⟩ =
        F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ m (hD (z : K) z.2)⟩ :=
      hinv γ ⟨(z : K), _⟩ ⟨pmoebius K₀ (ρ γ) (z : K), _⟩ rfl
    rw [hinv'] at h1
    show ((z : K) - (p : K)) ^ e * F ⟨(z : K), _⟩ = φ ⟨pmoebius K₀ (ρ γ) (z : K), _⟩ * Cinv (z : K) ^ e
    rw [← h1, ← hdiff' (z : K) z.2, mul_pow]
    ring

end S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc (solution)
