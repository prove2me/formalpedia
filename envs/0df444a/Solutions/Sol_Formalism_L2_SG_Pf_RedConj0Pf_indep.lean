-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:33.067728+00:00
-- url     : https://prove2.me/submissions/74f4991e-56df-4571-acef-15557a7ec39a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.L2.Host.restr_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution {b : Fin I.n → (Fin I.n → I.E)} (hb : ∀ i, b i ∈ I.L)
    (hsp : I.L ≤ Submodule.span (𝓞 I.E) (Set.range b) ⊔ w.asIdeal • I.L)
    (c : Fin I.n → 𝓞 I.E) (hc : ∑ j, c j • b j ∈ w.asIdeal • I.L) (j0 : Fin I.n) : c j0 ∈ w.asIdeal := by
  classical
  have hsm : ∀ (a : 𝓞 I.E) (v : Fin I.n → I.E), a • v = (a : I.E) • v := fun a v => by
    first | rfl | (ext i; simp [Algebra.smul_def])
  obtain ⟨r, hr1, hr⟩ : ∃ r : 𝓞 I.E, r - 1 ∈ w.asIdeal ∧
      ∀ x ∈ I.L, r • x ∈ Submodule.span (𝓞 I.E) (Set.range b) := by
    set S := Submodule.span (𝓞 I.E) (Set.range b) with hS
    have hfg : (I.L.map S.mkQ).FG := I.L_fg.map _
    have hle : I.L.map S.mkQ ≤ w.asIdeal • I.L.map S.mkQ := by
      rw [← Submodule.map_smul'']
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hq
      obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (hsp hx)
      refine Submodule.mem_map.2 ⟨t, ht, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      rw [show t - (s + t) = -s by abel]
      exact S.neg_mem hs
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul w.asIdeal _ hfg hle
    refine ⟨r, hr1, fun x hx => ?_⟩
    have h := hr _ (Submodule.mem_map_of_mem (f := S.mkQ) hx)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  have hrw : r ∉ w.asIdeal := by
    intro h
    have h1 : (1 : 𝓞 I.E) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem h hr1
      simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hr0 : (r : I.E) ≠ 0 := by
    intro h
    apply hrw
    have : r = 0 := RingOfIntegers.ext (by simpa using h)
    rw [this]
    exact w.asIdeal.zero_mem
  have hspan : ⊤ ≤ Submodule.span I.E (Set.range b) := by
    rw [← I.L_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have h1 : r • x ∈ Submodule.span I.E (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 I.E) I.E (Set.range b) (hr x hx)
    have e : x = (r : I.E)⁻¹ • (r • x) := by
      rw [hsm, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ h1
  have hli : LinearIndependent I.E b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  have hmap : (I.L).map (r • LinearMap.id) ≤ Submodule.span (𝓞 I.E) (Set.range b) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr x hx
  have hrel : r • ∑ j, c j • b j ∈ w.asIdeal • Submodule.span (𝓞 I.E) (Set.range b) := by
    have h : r • ∑ j, c j • b j ∈ (w.asIdeal • I.L).map (r • LinearMap.id) := ⟨_, hc, rfl⟩
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl hmap h
  obtain ⟨d, hd, hdx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum w.asIdeal b _).1 hrel
  rw [Finsupp.sum_fintype _ _ (by simp)] at hdx
  have hsum : ∑ i, ((r * c i - d i : 𝓞 I.E) : I.E) • b i = 0 := by
    have e : ∑ i, ((r * c i - d i : 𝓞 I.E) : I.E) • b i = ∑ i, (r * c i - d i) • b i := by
      simp_rw [hsm]
    rw [e]
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdx, sub_self]
  have key := Fintype.linearIndependent_iff.1 hli (fun i => ((r * c i - d i : 𝓞 I.E) : I.E)) hsum j0
  have h0 : r * c j0 - d j0 = 0 := RingOfIntegers.ext (by simpa using key)
  have hmem : r * c j0 ∈ w.asIdeal := by rw [sub_eq_zero.1 h0]; exact hd j0
  exact (w.isPrime.mem_or_mem hmem).resolve_left hrw
end Formalism.L2.SG.Pf.RedConj0Pf
