-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.germIdentityOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:55.281039+00:00
-- url     : https://prove2.me/submissions/7c127126-dd10-4e48-9478-8ebd9781651f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_compact_mul_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_lat_inf
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_exists_lat_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cut_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cutSet_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_amp_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_amp_latInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_intLat_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_core2
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cut_Q
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cut_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_shift_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.GermSumLattices
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.GermIdentityAssemble := by
  intro hGH hGK hKH hA2 hMMp hRF hSU hSS hCS hRC hSN hPD hLC hML hIR hCV hXV K _ _ _ R ψ hD hn m hm
    n₀ F hF Om Sg Λ hOm hΛ hOmΛ hNs hψ
  classical
  have iA := hD.artin
  have iR := hD.red
  obtain ⟨γ, hγ⟩ := hGH K R ψ hD hn m
  have hMM : MM R := hMMp K R ψ hD
  have hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w') := hKH K R ψ
  have hψR : ∀ r ∈ R, ψ r = 1 := by
    intro r hr
    have h1 := (hD.selfDual 1).2 R.one_mem r hr
    rwa [one_mul] at h1
  have hs : IsUnit ((m + 1 : ℕ) : K) := hn (m + 1) (Nat.succ_ne_zero m)
  have hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite := hRF K (m + 1) (by omega)
  obtain ⟨μ, hμ⟩ : ∃ μ : Finset Kˣ, ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1 :=
    ⟨(hroots 1).toFinset, fun ζ => by simp⟩
  have h1μ : (1 : Kˣ) ∈ μ := (hμ 1).2 (one_pow _)
  have hOmc : IsCompact Om := hOm.2.1
  have hOmU : ∀ z ∈ Om, IsUnit z := hOm.2.2.1
  have hμOm : ∀ z ∈ Om, ∀ ζ ∈ μ, (ζ : K) * z ∈ Om := by
    intro z hz ζ hζ
    refine hOm.2.2.2 z hz ζ ?_
    rw [← Units.val_pow_eq_pow_val, (hμ ζ).1 hζ, Units.val_one]

  obtain ⟨Q, hQdef⟩ : ∃ Q : Set K, Q = (fun z : K => (-1) ^ m * z ^ (m + 1)) '' Om := ⟨_, rfl⟩
  have hQc : IsCompact Q := by
    rw [hQdef]
    exact hOmc.image (by fun_prop)
  have hQu : ∀ d ∈ Q, IsUnit d := by
    rw [hQdef]
    rintro _ ⟨z, hz, rfl⟩
    exact ((isUnit_one.neg).pow m).mul ((hOmU z hz).pow _)

  choose VG hVG hVG' using fun h : Point K => hGK K R ψ hD hn m hm γ hγ h Q hQc hQu
  choose ΛL hΛL hΛL' using fun h : Point K =>
    hLC K R ψ hD hn (m + 1) h Om (by omega) hOmc hOmU
  obtain ⟨Esq, hEsq, hsq⟩ := hSN K R ψ hD hn
  obtain ⟨ΛM, hΛM, hΛM'⟩ := hML K R ψ hD hn Om hOmc hOmU Esq hEsq

  obtain ⟨Λ', hΛ'lat, hΛ'le, hΛ'M⟩ := exists_lat_le (F ×ˢ μ)
    (fun p => (ΛL p.1).comap (AddMonoidHom.mulLeft (p.2 : K)))
    (fun p _ => (hΛL p.1).1.preimage (continuous_const.mul continuous_id))
    (lat_inf hΛ hΛM.1)
  have hΛ'Λ : Λ' ≤ Λ := hΛ'le.trans inf_le_left
  have hΛ'ΛM : Λ' ≤ ΛM := hΛ'le.trans inf_le_right
  have hΛ'ζ : ∀ h ∈ F, ∀ ζ ∈ μ, ∀ l ∈ Λ', (ζ : K) * l ∈ ΛL h := by
    intro h hh ζ hζ l hl
    exact hΛ'M (h, ζ) (Finset.mem_product.2 ⟨hh, hζ⟩) hl
  have hΛ'1 : ∀ h ∈ F, ∀ l ∈ Λ', l ∈ ΛL h := by
    intro h hh l hl
    have h1 := hΛ'ζ h hh 1 h1μ l hl
    rwa [Units.val_one, one_mul] at h1
  have hst : ∀ z ∈ Om, ∀ l ∈ Λ', z + l ∈ Om := fun z hz l hl => hOmΛ z hz l (hΛ'Λ hl)
  have hML' : ∀ z ∈ Om, ∀ l ∈ Λ', IsUnit (z + l) ∧ modK R (z + l) = modK R z ∧
      l * Ring.inverse z ∈ Esq := fun z hz l hl => hΛM' z hz l (hΛ'ΛM hl)
  obtain ⟨VCV, hVCV, hCV'⟩ := hCV K R ψ hD hn m hm Om Λ' hOm hΛ'lat hst
    (fun z hz l hl => (hML' z hz l hl).2.1)
  choose EX hEX VX hVX hXX using fun (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1) (h2 : ζ ≠ 1) =>
    hXV K R ψ hD hn m hm Om Λ' Sg ζ hOm hΛ'lat hst h1 h2
  obtain ⟨EXs, hEXs, hEXs'⟩ : ∃ E ∈ 𝓝 (0 : K), ∀ x ∈ E, ∀ (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1)
      (h2 : ζ ≠ 1), x ∈ EX ζ h1 h2 := by
    refine ⟨⋂ ζ ∈ μ, (if hh : ζ ^ (m + 1) = 1 ∧ ζ ≠ 1 then EX ζ hh.1 hh.2 else Set.univ),
      (Filter.biInter_finset_mem μ).2 (fun ζ _ => ?_), ?_⟩
    · split_ifs with hh
      · exact hEX ζ hh.1 hh.2
      · exact Filter.univ_mem
    · intro x hx ζ h1 h2
      have h3 := Set.mem_iInter₂.1 hx ζ ((hμ ζ).2 h1)
      rwa [dif_pos ⟨h1, h2⟩] at h3
  obtain ⟨VXs, hVXs, hVXs'⟩ : ∃ E ∈ 𝓝 (0 : K), ∀ x ∈ E, ∀ (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1)
      (h2 : ζ ≠ 1), x ∈ VX ζ h1 h2 := by
    refine ⟨⋂ ζ ∈ μ, (if hh : ζ ^ (m + 1) = 1 ∧ ζ ≠ 1 then VX ζ hh.1 hh.2 else Set.univ),
      (Filter.biInter_finset_mem μ).2 (fun ζ _ => ?_), ?_⟩
    · split_ifs with hh
      · exact hVX ζ hh.1 hh.2
      · exact Filter.univ_mem
    · intro x hx ζ h1 h2
      have h3 := Set.mem_iInter₂.1 hx ζ ((hμ ζ).2 h1)
      rwa [dif_pos ⟨h1, h2⟩] at h3
  obtain ⟨EP, hEP, VP, hVP, hP⟩ := hPD K R ψ hD hn m Om Sg hOmc
  obtain ⟨ELC, hELC, hELC'⟩ := compact_mul_small hOmc (hΛ'lat.1.mem_nhds Λ'.zero_mem)

  obtain ⟨E1, hE1, W1, hW1, hEW⟩ : ∃ E1 ∈ 𝓝 (0 : K), ∃ W1 ∈ 𝓝 (0 : K), ∀ a ∈ E1, ∀ b ∈ W1,
      a * (1 + b) + b ∈ Esq := by
    have hc : Continuous (fun p : K × K => p.1 * (1 + p.2) + p.2) := by fun_prop
    have ht : Tendsto (fun p : K × K => p.1 * (1 + p.2) + p.2) (𝓝 ((0 : K), (0 : K)))
        (𝓝 (0 : K)) := by
      simpa using hc.tendsto ((0 : K), (0 : K))
    have h1 := ht hEsq
    rw [nhds_prod_eq] at h1
    obtain ⟨E1, hE1, W1, hW1, hsub⟩ := Filter.mem_prod_iff.1 h1
    exact ⟨E1, hE1, W1, hW1, fun a ha b hb => hsub (show ((a, b) : K × K) ∈ E1 ×ˢ W1 from ⟨ha, hb⟩)⟩
  obtain ⟨W2, hW2, hW2'⟩ := compact_mul_small
    (C := (((Sg ×ˢ Sg).image (fun p : K × K => p.1 - p.2) : Finset K) : Set K))
    (Finset.finite_toSet _).isCompact hW1
  obtain ⟨VR, hVR, hR⟩ := hRC K R ψ hD hn m Sg (EP ∩ ELC ∩ E1 ∩ EXs)
    (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hEP hELC) hE1) hEXs)
  obtain ⟨VS, hVS, hS⟩ := hSS K R ψ hD hn Sg ((⋂ h ∈ F, VG h) ∩ VCV ∩ W2)
    (Filter.inter_mem (Filter.inter_mem ((Filter.biInter_finset_mem F).2 fun h _ => hVG h) hVCV)
      hW2)
  obtain ⟨VU, hVU, hU⟩ := hSU K R ψ hD hn Sg
  obtain ⟨VC, hVC, hC⟩ := hCS K R ψ hD hn m hm Om Sg hOm
  refine ⟨VS ∩ VU ∩ VC ∩ VR ∩ VP ∩ VXs, Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
    (Filter.inter_mem (Filter.inter_mem hVS hVU) hVC) hVR) hVP) hVXs, ?_⟩
  rintro t t₁ t₂ cr ⟨⟨⟨⟨⟨htS, htU⟩, htC⟩, htR⟩, htP⟩, htX⟩ hcr σ hσ σ' hσ' hsh1 hsh2 h hh h' hh'
  obtain ⟨κ, hκ, ⟨⟨⟨hκP, hκLC⟩, hκ1⟩, hκX⟩⟩ := hR t t₁ t₂ htR σ hσ σ' hσ' hsh1 hsh2
  obtain ⟨⟨ht1G, ht1CV⟩, -⟩ := hS t t₁ htS σ hσ hsh1
  obtain ⟨⟨ht2G, -⟩, ht2W⟩ := hS t t₂ htS σ' hσ' hsh2
  have hcut1 : cutSet m Om t₁ = cutSet m Om t := (hC t htC).1 σ hσ t₁ hsh1
  have hcut2 : cutSet m Om t₂ = cutSet m Om t := (hC t htC).1 σ' hσ' t₂ hsh2
  have hSfin : {x | (cr x : K) ∈ cutSet m Om t}.Finite :=
    cut_finite R hD.isOpen (cutSet_compact m hOmc t) cr hcr
  have hmod : ∀ (t' : Kˣ) (τ : K), τ ∈ Sg → IsShift t t' τ → modK R (t' : K) = modK R (t : K) := by
    intro t' τ hτ hsh
    have h1 := (hU t htU τ hτ).2
    rw [← hsh, mm_inv hMM, mm_inv hMM] at h1
    exact inv_injective h1
  obtain ⟨b, hb⟩ := hsq (κ * t₂ * t₁⁻¹) (by
    have h1 := hEW _ hκ1 _ (hW2' (σ - σ') (by
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨(σ, σ'), Finset.mem_product.2 ⟨hσ, hσ'⟩, rfl⟩) _ ht2W)
    have h2 := shift_ratio t t₁ t₂ σ σ' hsh1 hsh2
    have h3 : ((κ * t₂ * t₁⁻¹ : Kˣ) : K) - 1 =
        ((κ : K) - 1) * (1 + (σ - σ') * (t₂ : K)) + (σ - σ') * (t₂ : K) := by
      rw [mul_assoc, Units.val_mul, h2]
      ring
    rw [h3]
    exact h1)
  have hGinv : LatInv Λ Om (fun z => NsK R ψ (m + 1) h h' z * ψ (z * (σ - σ'))) := by
    intro z hz l hl
    simp only
    rw [hNs h hh h' hh' z hz l hl, add_mul, AddChar.map_add_eq_mul, hψ σ hσ σ' hσ' l hl, mul_one]
  refine core2 R ψ m γ hMM hD.unitary hψR hs hγ.1 hγ.2.1 h h' t₁ t₂ κ cr (cutSet m Om t) Om μ hμ
    hSfin hroots hherm ?_ ?_ hκ ((hmod t₂ σ' hσ' hsh2).trans (hmod t₁ σ hσ hsh1).symm) b hb ?_ hμOm
    ?_ (σ - σ') (hP t t₁ t₂ κ htP σ hσ σ' hσ' hsh1 hsh2 hκ hκP) ?_ _ ?_
  · intro x hx w'
    refine hVG' h t₁ (cr x) (Set.mem_iInter₂.1 ht1G h hh) ?_ w'
    rw [hQdef]
    exact cut_Q m Om t₁ (cr x) (hcut1 ▸ hx)
  · intro x hx w'
    refine hVG' h' t₂ (cr x) (Set.mem_iInter₂.1 ht2G h' hh') ?_ w'
    rw [hQdef]
    exact cut_Q m Om t₂ (cr x) (hcut2 ▸ hx)
  · intro x hx z hz
    exact cut_mem m Om hOm t₁ (cr x) z (hcut1 ▸ hx) hz
  · intro z hz w'
    refine hΛL' h' z (κ * z) hz ?_ w'
    have h1 := hΛ'1 h' hh' _ (hELC' _ hz _ hκLC)
    have h2 : ((κ * z : Kˣ) : K) - (z : K) = (z : K) * ((κ : K) - 1) := by
      rw [Units.val_mul]
      ring
    rw [h2]
    exact h1
  · intro ζ hζ hne
    have hζ1 := (hμ ζ).1 hζ
    refine hXX ζ hζ1 hne t t₁ t₂ κ cr (amp R ψ m γ h h' t₁ ζ) (hVXs' _ htX ζ hζ1 hne) σ hσ σ' hσ'
      hsh1 hsh2 hκ (hEXs' _ hκX ζ hζ1 hne) hcr ?_ ?_
    · exact amp_latInv R ψ m γ h h' t₁ ζ Om Esq Λ' (ΛL h) (ΛL h') hγ.2.1 hherm hOmU hML' hsq
        (hΛL' h) (hΛL' h') (hΛ'1 h hh) (hΛ'ζ h' hh' ζ hζ) (fun z hz => hμOm z hz ζ hζ)
    · intro z _ hne0
      rw [amp_unit] at hne0
      refine hA2 K R ψ hD (m + 1) (by omega) h h' z (ζ * z) ((hF h hh).trans (hF h' hh').symm) ?_
      unfold Ns
      refine mul_ne_zero ?_ (right_ne_zero_of_mul hne0)
      rw [(hMM z (ζ * z)).2]
      exact_mod_cast (pow_pos (mul_pos (hMM z z).1 (hMM (ζ * z) z).1) _).ne'
  · have hf1 : LatInv Λ' Om (f1 R ψ m h h' (σ - σ')) := by
      intro z hz l hl
      unfold f1
      rw [(hML' z hz l hl).2.1]
      congr 1
      exact hGinv z hz l (hΛ'Λ hl)
    have h1 := hCV' t₁ cr (f1 R ψ m h h' (σ - σ')) ht1CV hcr hf1
    rw [hcut1] at h1
    rw [h1]
    congr 1
    rw [← hIR K R ψ hD Λ Λ' Om _ hΛ hΛ'lat hΛ'Λ hOmc hOmΛ hGinv]
    apply intLat_smul
    intro z hz
    obtain ⟨u, rfl⟩ := hOmU z hz
    have hNz : 0 < modK R (u : K) := (hMM u u).1
    unfold f1
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp
end Formalism.FourierDecayAlt.P
