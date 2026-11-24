-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.vd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:34.842999+00:00
-- url     : https://prove2.me/submissions/6e680cd7-6443-4624-9fab-090a30495b02

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_mu_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_discrIdeal_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_exists_pow_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_locF_inf_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_relIndex_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_absNorm_discrIdeal_of_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_eq_tprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_eq_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_vd_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_discrIdeal_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_vd_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vd_locF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (hF : IsFixF K F) [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (hN : Submodule.IsLattice K N) (h𝔭 : 𝔭.IsMaximal) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup * Ideal.absNorm 𝔭 ^ vd h M 𝔭 =
      Ideal.absNorm 𝔭 ^ vd h (M ⊓ locF 𝔭 N) 𝔭 := by
  set M'' := M ⊓ locF 𝔭 N with hM''
  set n := M''.toAddSubgroup.relIndex M.toAddSubgroup with hn
  have hn0 : n ≠ 0 := relIndex_ne_zero hM hN 𝔭
  obtain ⟨r, hr⟩ := exists_pow_smul h𝔭 hM hN
  have hle : M'' ≤ M := inf_le_left
  have hnorm := BallB.absNorm_discrIdeal_of_le hK hMi (Module.finBasis K V) n M'' hle rfl hn0
  rw [BrA.discrIdeal_eq_map hF hs M'', BrA.discrIdeal_eq_map hF hs M, BrA.absNorm_map hK hF,
    BrA.absNorm_map hK hF, ← mul_pow] at hnorm
  have hnorm' : Ideal.absNorm (BrA.discrF F h M'') = n * Ideal.absNorm (BrA.discrF F h M) :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hnorm
  have hD : BrA.discrF F h M ≠ ⊥ := by
    intro hb
    apply LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hM hMi
    rw [BrA.discrIdeal_eq_map hF hs M, hb, Ideal.map_bot]
  have hdvd : BrA.discrF F h M ∣ BrA.discrF F h M'' := by
    rw [Ideal.dvd_iff_le]
    exact Ideal.comap_mono (discrIdeal_mono hle)
  obtain ⟨J, hJ⟩ := hdvd
  have hDn : Ideal.absNorm (BrA.discrF F h M) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hJn : Ideal.absNorm J = n := by
    rw [hJ, map_mul, mul_comm] at hnorm'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hDn) hnorm'
  have hJ0 : J ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot] at hJn
    exact hn0 hJn.symm
  have hother : ∀ 𝔮 : {𝔮 : Ideal (𝓞 F) // 𝔮.IsMaximal}, 𝔮.1 ≠ 𝔭 → mu 𝔮.1 J = 0 := by
    intro 𝔮 hne
    have e1 : vd h M'' 𝔮.1 = vd h M 𝔮.1 := by
      rw [← localizedQuotients.vd_locF hF h M'' 𝔮.2, hM'', locF_inf_of_ne h𝔭 𝔮.2 hne hr, localizedQuotients.vd_locF hF h M 𝔮.2]
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ] at e1
    change mu 𝔮.1 (_ * J) = mu 𝔮.1 _ at e1
    rw [mu_mul 𝔮.2 hD hJ0] at e1
    omega
  have hJn' : Ideal.absNorm J = Ideal.absNorm 𝔭 ^ mu 𝔭 J := by
    have := BrA.absNorm_eq_tprod hJ0
    rw [tprod_eq_mulSingle ⟨𝔭, h𝔭⟩] at this
    · have h3 : (Ideal.absNorm J : ℝ) = ((Ideal.absNorm 𝔭 ^ mu 𝔭 J : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact this
      exact_mod_cast h3
    · intro 𝔮 hne
      rw [show sSup {e : ℕ | J ≤ 𝔮.1 ^ e} = mu 𝔮.1 J from rfl,
        hother 𝔮 (fun h => hne (Subtype.ext h)), pow_zero]
  have hvd : vd h M'' 𝔭 = vd h M 𝔭 + mu 𝔭 J := by
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ]
    exact mu_mul h𝔭 hD hJ0
  rw [hvd, pow_add, ← hJn', hJn, mul_comm]
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
