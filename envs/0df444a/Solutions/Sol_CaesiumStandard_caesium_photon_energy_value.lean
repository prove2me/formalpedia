-- Prove2me | solution 1 for CaesiumStandard.caesium_photon_energy_value
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:02:57.943846+00:00
-- url     : https://prove2.me/submissions/2a34c9bb-8a2e-44b8-b7bc-c3286743141a

import Definitions.Def_CaesiumStandard_constants

open CaesiumStandard

theorem W4a_CaesiumStandard_indep :
    (∀ nu₁ nu₂ : ℚ, moleIn nu₁ = moleIn nu₂)
    ∧ (∀ nu₁ nu₂ : ℚ, coulombIn nu₁ = coulombIn nu₂)
    ∧ (∀ nu₁ nu₂ : ℚ, 0 < nu₁ → 0 < nu₂ → nu₁ ≠ nu₂ →
        secondIn nu₁ ≠ secondIn nu₂
        ∧ metreIn nu₁ ≠ metreIn nu₂
        ∧ kilogramIn nu₁ ≠ kilogramIn nu₂
        ∧ ampereIn nu₁ ≠ ampereIn nu₂
        ∧ kelvinIn nu₁ ≠ kelvinIn nu₂
        ∧ candelaIn nu₁ ≠ candelaIn nu₂) := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro nu₁ nu₂ h1 h2 hne
  have lin : ∀ (f : ℚ → ℚ), (∀ nu, f nu = f 1 * nu) → f 1 ≠ 0 → f nu₁ ≠ f nu₂ := by
    intro f hf h0 h
    rw [hf nu₁, hf nu₂] at h
    exact hne (mul_left_cancel₀ h0 h)
  have inv : ∀ (f : ℚ → ℚ), (∀ nu, f nu = f 1 / nu) → f 1 ≠ 0 → f nu₁ ≠ f nu₂ := by
    intro f hf h0 h
    rw [hf nu₁, hf nu₂, div_eq_div_iff h1.ne' h2.ne'] at h
    exact hne (mul_left_cancel₀ h0 h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    unfold secondIn at h
    rw [div_eq_div_iff h1.ne' h2.ne'] at h
    apply hne
    linarith
  · exact inv _ (fun nu => by unfold metreIn; ring) (by norm_num [metreIn, cLight])
  · exact lin _ (fun nu => by unfold kilogramIn; ring) (by norm_num [kilogramIn, hPlanck, cLight])
  · exact lin _ (fun nu => by unfold ampereIn; ring) (by norm_num [ampereIn, eCharge])
  · exact lin _ (fun nu => by unfold kelvinIn; ring) (by norm_num [kelvinIn, hPlanck, kBoltzmann])
  · intro h
    have hf : ∀ nu, candelaIn nu = candelaIn 1 * nu ^ 2 := fun nu => by unfold candelaIn; ring
    have h0 : candelaIn 1 ≠ 0 := by norm_num [candelaIn, hPlanck, kcdLumEff]
    rw [hf nu₁, hf nu₂] at h
    have h' := mul_left_cancel₀ h0 h
    exact hne ((pow_left_inj₀ h1.le h2.le two_ne_zero).mp h')

theorem W4a_CaesiumStandard_katal :
    nAvogadro * tCs = 6.02214076e14 / 9.19263177 := by
  norm_num [nAvogadro, tCs, dnuCs]

theorem W4a_CaesiumStandard_optical :
    tOpt = (50 / 27) * 1e-15
    ∧ lambdaOpt = (14.9896229 / 27) * 1e-6
    ∧ EOpt = 3.578077881e-19
    ∧ luminousEnergyPerPhotonOpt = 2.443827192723e-16
    ∧ (1e6 / 2.246520349221536260971) * (luminousEnergyPerPhotonOpt * dnuCs) = 1
    ∧ (8.9875517873681764e2 / 1.898410313566852566340456048807087002459)
        * (luminousEnergyPerPhotonOpt * dnuCs / lambdaCs ^ 2) = 1 := by
  norm_num [tOpt, lambdaOpt, EOpt, luminousEnergyPerPhotonOpt, nuOpt, cLight, hPlanck,
    kcdLumEff, dnuCs, lambdaCs]

theorem W4a_CaesiumStandard_em :
    (1e19 / 1.602176634) * eCharge = 1
    ∧ (1.602176634e5 / 6.09110229711386655) * (ECs / eCharge) = 1
    ∧ (2.359720966701071721258310212e-4 / 6.09110229711386655) * (hPlanck / eCharge ^ 2) = 1
    ∧ (6.09110229711386655e4 / 2.359720966701071721258310212) * (eCharge ^ 2 / hPlanck) = 1
    ∧ (6.09110229711386655e14 / 2.566969966535569956) * (eCharge ^ 2 / ECs) = 1
    ∧ (1.602176634e15 / 6.62607015) * (hPlanck / eCharge) = 1
    ∧ (2.359720966701071721258310212e6 / 6.62607015) * (hPlanck * tCs / eCharge ^ 2) = 1
    ∧ (1.43996454705862285832702376e12 / 5.59932604907689089550702935)
        * (ECs * tCs / (eCharge * lambdaCs ^ 2)) = 1 := by
  norm_num [eCharge, ECs, hPlanck, dnuCs, tCs, lambdaCs, cLight]

theorem W4a_CaesiumStandard_efp :
    (1e24 / 6.09110229711386655) * ECs = 1
    ∧ (1e14 / 5.59932604907689089550702935) * (ECs * dnuCs) = 1
    ∧ (2.99792458e22 / 5.59932604907689089550702935) * (ECs / lambdaCs) = 1
    ∧ (2.6944002417373989539335912e19
        / 4.73168129737820913189287698892486811451620615) * (ECs / lambdaCs ^ 3) = 1
    ∧ (1 / 89875517873681764) * (ECs / MCs) = 1 := by
  norm_num [ECs, MCs, hPlanck, dnuCs, lambdaCs, cLight]

theorem W4a_CaesiumStandard_candela :
    (1e11 / 3.82433969151951648163130104605) * (hPlanck * dnuCs ^ 2 * kcdLumEff) = 1 := by
  norm_num [hPlanck, dnuCs, kcdLumEff]

theorem W4a_CaesiumStandard_kelvin :
    (13.80649 / 6.09110229711386655) * (hPlanck * dnuCs / kBoltzmann) = 1 := by
  norm_num [hPlanck, dnuCs, kBoltzmann]

theorem W4a_CaesiumStandard_ampere :
    (1e9 / 1.472821982686006218) * (eCharge * dnuCs) = 1 := by
  norm_num [eCharge, dnuCs]

theorem W4a_CaesiumStandard_kilogram :
    (8.9875517873681764e40 / 6.09110229711386655) * (hPlanck * dnuCs / cLight ^ 2) = 1 := by
  norm_num [hPlanck, dnuCs, cLight]

theorem W4a_CaesiumStandard_photon_mass :
    MCs = 6.09110229711386655e-40 / 8.9875517873681764 := by
  norm_num [MCs, ECs, hPlanck, dnuCs, cLight]

theorem solution :
    ECs = 6.09110229711386655e-24 := by
  norm_num [ECs, hPlanck, dnuCs]

theorem W4a_CaesiumStandard_wavelength :
    lambdaCs = 299792458 / 9192631770 ∧ 0.0326 < lambdaCs ∧ lambdaCs < 0.0327 := by
  norm_num [lambdaCs, cLight, dnuCs]

theorem W4a_CaesiumStandard_second :
    9192631770 * tCs = 1 ∧ tCs = 1 / 9192631770 := by
  norm_num [tCs, dnuCs]

theorem W4a_CaesiumStandard_base :
    9192631770 / dnuCs = 1
    ∧ (9192631770 / 299792458) * (cLight / dnuCs) = 1
    ∧ (8.9875517873681764e40 / 6.09110229711386655) * (hPlanck * dnuCs / cLight ^ 2) = 1
    ∧ (1e9 / 1.472821982686006218) * (eCharge * dnuCs) = 1
    ∧ (13.80649 / 6.09110229711386655) * (hPlanck * dnuCs / kBoltzmann) = 1
    ∧ 6.02214076e23 / nAvogadro = 1
    ∧ (1e11 / 3.82433969151951648163130104605) * (hPlanck * dnuCs ^ 2 * kcdLumEff) = 1 := by
  norm_num [dnuCs, cLight, hPlanck, eCharge, kBoltzmann, nAvogadro, kcdLumEff]
