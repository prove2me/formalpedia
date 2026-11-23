-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.crossVanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:41.757883+00:00
-- url     : https://prove2.me/submissions/0feebad2-2fc6-494a-83b6-1a6d56481825

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mem_Pk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inter_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulU
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_powU
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_hensel
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_classes_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_roots_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_char_family
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_TT_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_TT_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_pow_mem_of_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_shift_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_unit_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_quot_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution : Formalism.FourierDecayAlt.A6.CrossVanish := by
  intro K _ _ _ R ψ hD hnat m hm Om Λ Sg ζ hOm hΛ hstab hζ hζ1
  obtain ⟨ϖ, hϖ, hex⟩ := hD.unif
  have h : Ctx K R ϖ := ⟨hD.t2, hD.isOpen, hD.isCompact, hϖ, hex, hD.red, hnat⟩
  have hart := hD.artin
  have hred := hD.red
  have hψR : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have := (hD.selfDual 1).2 R.one_mem r hr
    simpa using this
  obtain ⟨su, hsu⟩ := hnat (m + 1) (by omega)
  obtain ⟨θ, hθdef⟩ : ∃ θ : K, θ = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hθ : ((m + 1 : ℕ) : K) * θ = 1 := by rw [← hsu, hθdef]; simp
  have hsR : ((m + 1 : ℕ) : K) ∈ R := natCast_mem R _
  obtain ⟨a, ha⟩ := Pk_ex h θ
  obtain ⟨b₁, hb₁⟩ := bounded h hOm.2.1
  obtain ⟨b₂, hb₂⟩ := inv_bounded h hOm.2.1 hOm.2.2.1
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ, b = b₁ + b₂ := ⟨_, rfl⟩
  have hbz : ∀ z ∈ Om, z ∈ Pk R ϖ (-(b : ℤ)) := fun z hz => Pk_mono hϖ (by omega) (hb₁ z hz)
  have hbi : ∀ z ∈ Om, ∀ zi : K, z * zi = 1 → zi ∈ Pk R ϖ (-(b : ℤ)) :=
    fun z hz zi hzi => Pk_mono hϖ (by omega) (hb₂ z hz zi hzi)
  obtain ⟨l, hl⟩ := basis h (hΛ.1.mem_nhds Λ.zero_mem)
  obtain ⟨d, hd⟩ := bounded h Sg.finite_toSet.isCompact
  obtain ⟨e₁, he₁⟩ := Pk_ex h (ζ : K)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (1 - (ζ : K)) ∉ Pk R ϖ N₀ := by
    by_contra hcon
    push Not at hcon
    have h0 := inter_zero h hcon
    apply hζ1
    ext
    rw [Units.val_one]
    linear_combination -h0
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = m * b := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = N₀ + a + b := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = N + e₁ + q + b := ⟨_, rfl⟩
  obtain ⟨big, hbig⟩ : ∃ big : ℕ, big = a + 1 + l + b := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : ℕ, v₁ = M + a + big + N + q + b + e₁ := ⟨_, rfl⟩
  have hpm : ∀ zi ∈ Pk R ϖ (-(b : ℤ)), zi ^ m ∈ Pk R ϖ (-(q : ℤ)) := fun zi hzi => by
    have := Pk_pow hzi m
    convert this using 2; rw [hq]; push_cast; ring
  have hps : ∀ zi ∈ Pk R ϖ (-(b : ℤ)), zi ^ (m + 1) ∈ Pk R ϖ (-((q : ℤ) + b)) := fun zi hzi => by
    have := Pk_pow hzi (m + 1)
    convert this using 2; rw [hq]; push_cast; ring
  have omΛ : ∀ z ∈ Om, ∀ w ∈ Pk R ϖ ((l : ℤ) + b), z * w ∈ Λ := fun z hz w hw => hl _ (by
    have := Pk_mul (hbz z hz) hw
    convert this using 2; ring)
  have omO : ∀ z ∈ Om, ∀ w ∈ Pk R ϖ ((l : ℤ) + b), z * (1 + w) ∈ Om := fun z hz w hw => by
    have := hstab z hz _ (omΛ z hz w hw)
    convert this using 1; ring
  obtain ⟨BB, hBcard, hBmem, hBsum⟩ := char_family (Pk R ϖ (-(N : ℤ))) (Pk R ϖ ((e₁ : ℤ) + b))
    (quot_finite h _ _)
  refine ⟨(Pk R ϖ (M : ℤ) : Set K), (Pk_isOpen h _).mem_nhds (Pk R ϖ _).zero_mem,
    (Pk R ϖ ((v₁ : ℤ) + d) : Set K), (Pk_isOpen h _).mem_nhds (Pk R ϖ _).zero_mem, ?_⟩
  intro t t₁ t₂ κ cr g ht σ hσ σ' hσ' hs₁ hs₂ _ hκE hcr hg hsupp
  have cut_mul : ∀ c ∈ cutSet m Om t, ∀ w ∈ Pk R ϖ ((l : ℤ) + b),
      (1 + w) ^ (m + 1) * c ∈ cutSet m Om t := by
    rintro c ⟨z, hz, hzc⟩ w hw
    exact ⟨z * (1 + w), omO z hz w hw, by rw [mul_pow, hzc]; ring⟩
  obtain ⟨μ₁, hμ₁, ht₁, hi₁, hσt₁⟩ := shift_facts h (n := (v₁ : ℤ)) (by omega)
    (hd σ (Finset.mem_coe.2 hσ)) ht hs₁
  obtain ⟨μ₂, hμ₂, ht₂, hi₂, hσt₂⟩ := shift_facts h (n := (v₁ : ℤ)) (by omega)
    (hd σ' (Finset.mem_coe.2 hσ')) ht hs₂
  have ht₁P : (t₁ : K) ∈ Pk R ϖ (v₁ : ℤ) := by
    rw [ht₁]
    exact Pk_smul (Pk_mono hϖ (by omega) ht) (R.add_mem R.one_mem (Pk_R hϖ (by omega) hμ₁))
  have hnt₁P : -(t₁ : K) ∈ Pk R ϖ (v₁ : ℤ) := (Pk R ϖ _).neg_mem ht₁P
  have e₁₁ : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₁
  have e₂₂ : (t₂ : K) * ((t₂⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₂
  have hq12 : (t₁ : K) * ((t₂⁻¹ : Kˣ) : K) = (1 + μ₁) * (1 + σ' * t) := by
    linear_combination ((t₂⁻¹ : Kˣ) : K) * ht₁ - (t : K) * (1 + μ₁) * ((t₂⁻¹ : Kˣ) : K) * hi₂ -
      (1 + σ' * t) * (1 + μ₁) * ((t₂⁻¹ : Kˣ) : K) * ht₂ + (1 + σ' * t) * (1 + μ₁) * e₂₂
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : K, ρ = (κ : K) * ((t₁ : K) * ((t₂⁻¹ : Kˣ) : K)) := ⟨_, rfl⟩
  have hρ : ρ - 1 ∈ Pk R ϖ (M : ℤ) := by
    rw [hρdef, hq12]
    refine mulU h (by omega) hκE (mulU h (by omega) ?_ ?_)
    · simpa using Pk_mono hϖ (by omega) hμ₁
    · simpa using Pk_mono hϖ (by omega) hσt₂
  have hρR : ρ ∈ R := by
    have := R.add_mem (Pk_R hϖ (by omega) hρ) R.one_mem
    simpa using this
  obtain ⟨A, hA⟩ : ∃ A : K, A = ((m + 1 : ℕ) : K) * ((t₁⁻¹ : Kˣ) : K) -
      ((m + 1 : ℕ) : K) * (ζ : K) * (κ : K) * ((t₂⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hAt : A * (t₁ : K) = ((m + 1 : ℕ) : K) * (1 - (ζ : K) * ρ) := by
    rw [hA, hρdef]
    linear_combination ((m + 1 : ℕ) : K) * e₁₁
  have h1ζ : (1 - (ζ : K)) ∈ Pk R ϖ (-(e₁ : ℤ)) :=
    (Pk R ϖ _).sub_mem (Pk_mono hϖ (by omega) (Pk_zero.2 R.one_mem)) he₁
  have root_mem : ∀ c : Kˣ, (c : K) ∈ cutSet m Om t → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c →
      (z : K) ∈ Om := by
    have hμ'' : (1 + μ₁) ^ m - 1 ∈ Pk R ϖ (v₁ : ℤ) := powU h (by omega) (by simpa using hμ₁) m
    have hy' : θ * ((1 + μ₁) ^ m - 1) ∈ Pk R ϖ ((v₁ : ℤ) - a) := by
      have := Pk_mul ha hμ''
      convert this using 2; ring
    obtain ⟨v, hv, hveq⟩ := hensel h (m + 1) hθ ha (n := (v₁ : ℤ) - a) (by omega) hy'
    have hw' : θ * ((1 + μ₁) ^ m - 1) * v ∈ Pk R ϖ ((l : ℤ) + b) :=
      Pk_mono hϖ (by omega) (Pk_smul hy' hv)
    have hveq' : (1 + θ * ((1 + μ₁) ^ m - 1) * v) ^ (m + 1) = (1 + μ₁) ^ m := by
      rw [hveq]; linear_combination ((1 + μ₁) ^ m - 1) * hθ
    rintro c ⟨z₀, hz₀, hz₀c⟩ z hz
    have hzK : (z : K) ^ (m + 1) = (-(t₁ : K)) ^ m * c := by
      have := congrArg Units.val hz
      simpa using this
    have hz₁ := omO z₀ hz₀ _ hw'
    have hz₁p : (z₀ * (1 + θ * ((1 + μ₁) ^ m - 1) * v)) ^ (m + 1) = (z : K) ^ (m + 1) := by
      rw [mul_pow, hz₀c, hveq', hzK, ht₁, ← neg_mul, mul_pow]; ring
    obtain ⟨u₁, hu₁⟩ := hOm.2.2.1 _ hz₁
    have := hOm.2.2.2 _ hz₁ ((z : K) * ((u₁⁻¹ : Kˣ) : K))
      (by rw [mul_pow, ← hz₁p, ← hu₁, ← mul_pow]; simp)
    convert this using 1
    rw [← hu₁]; simp
  have hβ : ∀ z : Kˣ, (z : K) ∈ Om → g (z : K) ≠ 0 →
      A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m) ∈ R := by
    intro z hz hgz
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hzi : ((z⁻¹ : Kˣ) : K) ∈ Pk R ϖ (-(b : ℤ)) := hbi z hz _ (Units.mul_inv z)
    have hzim := hpm _ hzi
    have e : A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m) =
        -((1 - (ζ : K)) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) +
          (ζ : K) * ((ρ - 1) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) := by
      rw [show (-(t₁ : K)) ^ m = (-(t₁ : K)) ^ j * (-(t₁ : K)) by rw [hj, pow_succ]]
      linear_combination (-θ * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) * hAt -
        (1 - (ζ : K) * ρ) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m) * hθ
    rw [e]
    refine R.add_mem (R.neg_mem ?_) ?_
    · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hm1 : m = 1 := by omega
        have hζ2 : ζ * ζ = 1 := by
          have := hζ
          rw [hm1] at this
          rw [← this]; exact (sq ζ).symm
        have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
        have h3 := hsupp z hz hgz
        rw [mul_inv, hζi, Units.val_mul] at h3
        rw [hj0, hm1, pow_zero, pow_one, one_mul]
        convert h3 using 1; ring
      · have := Pk_mul h1ζ (Pk_mul (pow_mem_of_pos h (by omega) hnt₁P hjpos) hzim)
        exact Pk_R hϖ (by omega) this
    · have := Pk_mul he₁ (Pk_mul hρ (Pk_mul
        (Pk_zero.2 (R.pow_mem (Pk_R hϖ (by omega) hnt₁P) j)) hzim))
      exact Pk_R hϖ (by omega) this
  obtain ⟨F, hF⟩ : ∃ F : Kˣ → ℂ, F = fun z : Kˣ => g (z : K) * ψ (A * (z : K)) := ⟨_, rfl⟩
  have Fshift : ∀ z : Kˣ, (z : K) ∈ Om → ∀ w ∈ Pk R ϖ ((l : ℤ) + b), ∀ ω : Kˣ, (ω : K) = 1 + w →
      F (z * ω) = F z * ψ (A * (z : K) * w) := by
    intro z hz w hw ω hω
    rw [hF]
    show g ((z * ω : Kˣ) : K) * ψ (A * ((z * ω : Kˣ) : K)) = g z * ψ (A * z) * ψ (A * z * w)
    rw [Units.val_mul, hω, mul_add, mul_one, hg z hz _ (omΛ z hz w hw), mul_add,
      AddChar.map_add_eq_mul, mul_assoc A]
    ring
  have hω : ∀ c c' : Kˣ, (c' : K) - c ∈ R → (c : K) ∈ cutSet m Om t → (c' : K) ∈ cutSet m Om t ∧
      ∃ ω : Kˣ, c' = c * ω ^ (m + 1) ∧ ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c → F (z * ω) = F z := by
    intro c c' hcc hc
    have hcci : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := Units.mul_inv c
    have hciP : ((c⁻¹ : Kˣ) : K) ∈ Pk R ϖ ((v₁ : ℤ) + -((q : ℤ) + b)) := by
      obtain ⟨z₀, hz₀, hz₀c⟩ := hc
      obtain ⟨u₀, hu₀⟩ := hOm.2.2.1 z₀ hz₀
      have hzz : z₀ * ((u₀⁻¹ : Kˣ) : K) = 1 := by rw [← hu₀]; simp
      have e1 : (z₀ * ((u₀⁻¹ : Kˣ) : K)) ^ (m + 1) = 1 := by rw [hzz, one_pow]
      rw [mul_pow, hz₀c] at e1
      have e2 : ((c⁻¹ : Kˣ) : K) = (-(t : K)) ^ m * ((u₀⁻¹ : Kˣ) : K) ^ (m + 1) := by
        linear_combination -((c⁻¹ : Kˣ) : K) * e1 +
          ((-(t : K)) ^ m * ((u₀⁻¹ : Kˣ) : K) ^ (m + 1)) * hcci
      rw [e2]
      exact Pk_mul (pow_mem_of_pos h (by omega)
        ((Pk R ϖ _).neg_mem (Pk_mono hϖ (by omega) ht)) hm) (hps _ (hbi z₀ hz₀ _ hzz))
    have hy : θ * (((c' : K) - c) * ((c⁻¹ : Kˣ) : K)) ∈ Pk R ϖ ((v₁ : ℤ) - q - b - a) := by
      have := Pk_mul ha (Pk_smul' hcc hciP)
      convert this using 2; ring
    obtain ⟨v, hv, hveq⟩ := hensel h (m + 1) hθ ha (n := (v₁ : ℤ) - q - b - a) (by omega) hy
    obtain ⟨w, hwdef⟩ : ∃ w : K, w = θ * (((c' : K) - c) * ((c⁻¹ : Kˣ) : K)) * v := ⟨_, rfl⟩
    rw [← hwdef] at hveq
    have hwP : w ∈ Pk R ϖ ((v₁ : ℤ) - q - b - a) := by rw [hwdef]; exact Pk_smul hy hv
    have hwl : w ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hwP
    obtain ⟨ω, _, hωv, _, _⟩ := unit_of h (k := (v₁ : ℤ) - q - b - a) (by omega) hwP
    have hc'eq : (c' : K) = (1 + w) ^ (m + 1) * c := by
      rw [hveq]
      linear_combination (-((c' : K) - c) * (c : K) * ((c⁻¹ : Kˣ) : K)) * hθ - ((c' : K) - c) * hcci
    refine ⟨by rw [hc'eq]; exact cut_mul _ hc _ hwl, ω, ?_, ?_⟩
    · ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hωv, hc'eq]; ring
    · intro z hz
      have hzO := root_mem c hc z hz
      rw [Fshift z hzO w hwl ω hωv]
      by_cases hgz : g (z : K) = 0
      · rw [hF]
        show g (z : K) * ψ (A * z) * _ = g (z : K) * ψ (A * z)
        rw [hgz]; simp
      · have hzK : (z : K) ^ (m + 1) = (-(t₁ : K)) ^ m * c := by
          have := congrArg Units.val hz
          simpa using this
        have hzzi : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
        have e1 : ((z : K) * ((z⁻¹ : Kˣ) : K)) ^ (m + 1) = 1 := by rw [hzzi, one_pow]
        rw [mul_pow, hzK] at e1
        have hci : ((c⁻¹ : Kˣ) : K) = (-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ (m + 1) := by
          linear_combination -((c⁻¹ : Kˣ) : K) * e1 +
            ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ (m + 1)) * hcci
        have e3 : A * (z : K) * w = (A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m)) *
            (((c' : K) - c) * v) := by
          rw [hwdef, hci, pow_succ]
          linear_combination (A * θ * (-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m *
            ((c' : K) - c) * v) * hzzi
        rw [e3, hψR _ (R.mul_mem (hβ z hzO hgz) (R.mul_mem hcc hv)), mul_one]
  have hB : ∀ β ∈ BB, ∃ lam : Kˣ, (lam : K) ∈ R ∧ ((lam⁻¹ : Kˣ) : K) ∈ R ∧
      ∀ c, TT (m + 1) (cutSet m Om t) ((-t₁) ^ m) F (lam * c) =
        TT (m + 1) (cutSet m Om t) ((-t₁) ^ m)
          (fun z => F z * ψ (A * (z : K) * ((t₁ : K) * β))) c := by
    intro β hβB
    have hε : (t₁ : K) * β ∈ Pk R ϖ ((v₁ : ℤ) + -(N : ℤ)) := Pk_mul ht₁P (hBmem β hβB)
    obtain ⟨υ, ε', hυ, hυi, hε'⟩ := unit_of h (by omega) hε
    have hεl : (t₁ : K) * β ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hε
    have hε'l : ε' ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hε'
    refine ⟨υ ^ (m + 1), ?_, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, hυ]
      exact R.pow_mem (R.add_mem R.one_mem (Pk_R hϖ (by omega) hε)) _
    · rw [← inv_pow, Units.val_pow_eq_pow_val, hυi]
      exact R.pow_mem (R.add_mem R.one_mem (Pk_R hϖ (by omega) hε')) _
    · refine TT_scale υ ?_ ?_
      · intro c
        rw [Units.val_mul, Units.val_pow_eq_pow_val, hυ]
        constructor
        · intro hc; exact cut_mul _ hc _ hεl
        · intro hc
          have := cut_mul _ hc _ hε'l
          have h1 : (1 + (t₁ : K) * β) * (1 + ε') = 1 := by
            rw [← hυ, ← hυi]; exact Units.mul_inv υ
          have h2 : (1 + ε') ^ (m + 1) * ((1 + (t₁ : K) * β) ^ (m + 1) * (c : K)) = c := by
            rw [← mul_assoc, ← mul_pow, mul_comm (1 + ε'), h1, one_pow, one_mul]
          rwa [h2] at this
      · intro c z hc hz
        exact Fshift z (root_mem c hc z hz) _ hεl υ hυ
  have hC : ∀ c : Kˣ, (c : K) ∈ cutSet m Om t → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c →
      ∑ β ∈ BB, F z * ψ (A * (z : K) * ((t₁ : K) * β)) = 0 := by
    intro c hc z hz
    have hzO := root_mem c hc z hz
    have hzP := hbz z hzO
    have hzzi : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
    have hziP := hbi z hzO _ hzzi
    obtain ⟨a', ha'⟩ : ∃ a' : K, a' = A * (t₁ : K) * z := ⟨_, rfl⟩
    have hsum := hBsum (ψ.compAddMonoidHom (AddMonoidHom.mulLeft a'))
      (by
        intro x hx
        show ψ (a' * x) = 1
        apply hψR
        have h1 : a' ∈ Pk R ϖ (-(e₁ : ℤ) + -(b : ℤ)) := by
          rw [ha', hAt]
          refine Pk_mul (Pk_smul' hsR ((Pk R ϖ _).sub_mem
            (Pk_mono hϖ (by omega) (Pk_zero.2 R.one_mem)) (Pk_smul he₁ hρR))) hzP
        exact Pk_R hϖ (by omega) (Pk_mul h1 hx))
      (by
        by_contra hcon
        push Not at hcon
        have h1 : a' ∈ Pk R ϖ (N : ℤ) := by
          rw [mem_Pk]
          refine (hD.selfDual _).1 fun r hr => ?_
          have h2 := hcon (((ϖ ^ (-(N : ℤ)) : Kˣ) : K) * r) (by
            rw [mem_Pk, ← mul_assoc, ← Units.val_mul, ← zpow_add]
            simpa using hr)
          have h3 : ψ (a' * (((ϖ ^ (-(N : ℤ)) : Kˣ) : K) * r)) = 1 := h2
          rw [← h3]; congr 1; ring
        have h4 : ((m + 1 : ℕ) : K) * ((ζ : K) * ((ρ - 1) * (z : K))) ∈ Pk R ϖ (N : ℤ) :=
          Pk_smul' hsR (Pk_mono hϖ (by omega) (Pk_mul he₁ (Pk_mul hρ hzP)))
        have h5 := Pk_mul ha (Pk_mul hziP ((Pk R ϖ _).add_mem h1 h4))
        apply hN₀
        have h6 : (1 - (ζ : K)) = θ * (((z⁻¹ : Kˣ) : K) *
            (a' + ((m + 1 : ℕ) : K) * ((ζ : K) * ((ρ - 1) * (z : K))))) := by
          rw [ha', hAt]
          linear_combination (-(1 - (ζ : K)) * ((m + 1 : ℕ) : K) * θ) * hzzi - (1 - (ζ : K)) * hθ
        rw [h6]
        exact Pk_mono hϖ (by omega) h5)
    rw [← Finset.mul_sum]
    have : ∑ β ∈ BB, ψ (A * (z : K) * ((t₁ : K) * β)) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun β _ => ?_
      show _ = ψ (a' * β)
      rw [ha']; congr 1; ring
    rw [this, mul_zero]
  have hfin1 : {x | (cr x : K) ∈ cutSet m Om t}.Finite := by
    have hcomp : IsCompact ((fun z : K => (-((t⁻¹ : Kˣ) : K)) ^ m * z ^ (m + 1)) '' Om) :=
      hOm.2.1.image (by fun_prop)
    refine (classes_finite h hcomp).subset ?_
    rintro x ⟨z, hz, hzc⟩
    refine ⟨cr x, ⟨z, hz, ?_⟩, hcr x⟩
    show (-((t⁻¹ : Kˣ) : K)) ^ m * z ^ (m + 1) = cr x
    rw [hzc, ← mul_assoc, ← mul_pow, neg_mul_neg, Units.inv_mul, one_pow, one_mul]
  have hmain := core hcr (TT_congr (R := R) hω) BB hBcard
    (fun β z => F z * ψ (A * (z : K) * ((t₁ : K) * β))) hB hC hfin1
    (fun D => roots_finite (m + 1) (by omega) D)
  refine Eq.trans (finsum_congr fun x => ?_) hmain
  unfold TT
  by_cases hc : (cr x : K) ∈ cutSet m Om t
  · rw [if_pos hc, if_pos hc]
    refine finsum_congr fun z => ?_
    by_cases hz : z ^ (m + 1) = (-t₁) ^ m * cr x
    · rw [if_pos hz, if_pos hz, hF, hA]
      show _ = g (z : K) * ψ _
      congr 2; ring
    · rw [if_neg hz, if_neg hz]
  · rw [if_neg hc, if_neg hc]
end Formalism.FourierDecayAlt.P.HenselRootsBounded
