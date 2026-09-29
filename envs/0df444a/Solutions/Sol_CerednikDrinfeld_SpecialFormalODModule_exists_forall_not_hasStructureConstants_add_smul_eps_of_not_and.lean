-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/25659833-3084-554a-ae9d-fccc35d11caa

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_apply_zero_eq_zero_and_ne_zero_of_not_and
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

noncomputable section

namespace VersalAsm

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem fst_comp_inl : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap k (DualNumber k)) = RingHom.id k :=
  RingHom.ext fun a => TrivSqZeroExt.fst_inl k a

theorem map_F_fst_eq (X₀ : FormalODModule q k) :
    (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F := by
  show (X₀.F.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F
  rw [MvFormalGroup.map_map_ringHom, fst_comp_inl, MvFormalGroup.map_ringHom_id']

theorem map_fst_eq (X₀ : FormalODModule q k) :
    (X₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀ := by
  rw [FormalODModule.map_map, fst_comp_inl, FormalODModule.map_id]

theorem comp_comp_j (j₀ : Zp2 q →+* k) :
    ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp j₀) = j₀ := by
  rw [← RingHom.comp_assoc, fst_comp_inl, RingHom.id_comp]

theorem dualNumber_eq (x : DualNumber k) :
    x = algebraMap k (DualNumber k) (TrivSqZeroExt.fst x) + TrivSqZeroExt.snd x • DualNumber.eps := by
  rw [← DualNumber.inr_eq_smul_eps]
  exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm

theorem snd_algebraMap_add_smul_eps (x y : k) :
    TrivSqZeroExt.snd (algebraMap k (DualNumber k) x + y • DualNumber.eps) = y := by
  rw [TrivSqZeroExt.snd_add, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.snd_inr]
  show TrivSqZeroExt.snd (TrivSqZeroExt.inl x : DualNumber k) + y = y
  rw [TrivSqZeroExt.snd_inl, zero_add]

theorem fst_algebraMap_add_smul_eps (x y : k) :
    TrivSqZeroExt.fst (algebraMap k (DualNumber k) x + y • DualNumber.eps) = x := by
  rw [TrivSqZeroExt.fst_add, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.fst_inr, add_zero]
  exact TrivSqZeroExt.fst_inl k x

theorem eq_of_algebraMap_add_smul_eps_eq {x : k} {y y' : k}
    (h : algebraMap k (DualNumber k) x + y • DualNumber.eps = algebraMap k (DualNumber k) x + y' • DualNumber.eps) : y = y' := by
  have := congrArg TrivSqZeroExt.snd h
  rwa [snd_algebraMap_add_smul_eps, snd_algebraMap_add_smul_eps] at this

theorem isHomogeneousVBasis_reduce (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (Y : FormalODModule q k) (hY : (X₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = Y)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = Y.F)
    (γ' : Fin 2 → CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ') :
    Y.IsHomogeneousVBasis (((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp j₀))
      (fun i => baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i)) := by
  subst hY
  exact hγ'.map (TrivSqZeroExt.fstHom k k k).toRingHom

theorem hasStructureConstants_reduce (X₀ : FormalODModule q k)
    (Y : FormalODModule q k) (hY : (X₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = Y)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = Y.F)
    (γ' : Fin 2 → CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (a' : ℕ → Fin 2 → DualNumber k) (ha' : (X₀.map (algebraMap k (DualNumber k))).HasStructureConstants γ' a') :
    Y.HasStructureConstants (fun i => baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i))
      (fun m i => TrivSqZeroExt.fst (a' m i)) := by
  subst hY
  exact ha'.map (TrivSqZeroExt.fstHom k k k).toRingHom

theorem exists_not_mem_span_pair (u₁ u₂ : Fin 3 → k) :
    ∃ δ : Fin 3 → k, ∀ v s : k, δ ≠ v • u₁ + s • u₂ := by
  classical
  have hlt : Module.finrank k (Submodule.span k ({u₁, u₂} : Set (Fin 3 → k))) < Module.finrank k (Fin 3 → k) := by
    calc Module.finrank k (Submodule.span k ({u₁, u₂} : Set (Fin 3 → k)))
        ≤ ({u₁, u₂} : Finset (Fin 3 → k)).card := by
          rw [← Finset.coe_pair]; exact finrank_span_finset_le_card _
      _ ≤ 2 := Finset.card_le_two
      _ < 3 := by norm_num
      _ = Module.finrank k (Fin 3 → k) := by simp
  have hne : Submodule.span k ({u₁, u₂} : Set (Fin 3 → k)) ≠ ⊤ := by
    intro h; rw [h, finrank_top] at hlt; exact lt_irrefl _ hlt
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 3 → k, δ ∉ Submodule.span k ({u₁, u₂} : Set (Fin 3 → k)) := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun x _ => hall x)
  refine ⟨δ, fun v s h => hδ ?_⟩
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem piIndex_zero_piIndex_zero (i : Fin 2) : FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := by
  ext; simp only [FormalODModule.piIndex_val]; omega

theorem piIndex_zero_ne (i : Fin 2) : FormalODModule.piIndex 0 i ≠ i := by
  intro h; have := congrArg Fin.val h; simp only [FormalODModule.piIndex_val] at this; omega

theorem piIndex_one (i : Fin 2) : FormalODModule.piIndex 1 i = i := by
  ext; simp only [FormalODModule.piIndex_val]; omega

theorem piIndex_two (i : Fin 2) : FormalODModule.piIndex 2 i = FormalODModule.piIndex 0 i := by
  ext; simp only [FormalODModule.piIndex_val]; omega

theorem piIndex_three (i : Fin 2) : FormalODModule.piIndex 3 i = i := by
  ext; simp only [FormalODModule.piIndex_val]; omega

end VersalAsm

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k)) :
    ∃ δa : ℕ → Fin 2 → k, (∀ i, δa 0 i = 0) ∧
      ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
        (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
            ((algebraMap k (DualNumber k)).comp j₀) γ' →
        ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
            (fun m i => algebraMap k (DualNumber k) (a m i) + δa m i • DualNumber.eps) := by
  classical

  obtain ⟨i₀, ha0, hu⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_apply_zero_eq_zero_and_ne_zero_of_not_and X₀ hsmooth γ hγ a ha h01

  obtain ⟨δ, hδ⟩ := VersalAsm.exists_not_mem_span_pair (k := k)
    ![a 0 (FormalODModule.piIndex 0 i₀), -(a 0 (FormalODModule.piIndex 0 i₀) ^ q), -(a 1 i₀ ^ q)]
    ![-(a 1 i₀), -(a 1 (FormalODModule.piIndex 0 i₀)), -(a 2 i₀)]
  refine ⟨fun m i => if m = 1 ∧ i = i₀ then δ 0 else if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1
      else if m = 2 ∧ i = i₀ then δ 2 else 0, fun i => by simp, ?_⟩
  intro γ' hγ' hcon
  have hne : FormalODModule.piIndex 0 i₀ ≠ i₀ := VersalAsm.piIndex_zero_ne i₀

  have hF := VersalAsm.map_F_fst_eq (q := q) X₀.toFormalODModule
  have hγb : X₀.toFormalODModule.IsHomogeneousVBasis j₀ (fun i => MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i)) := by
    have := VersalAsm.isHomogeneousVBasis_reduce j₀ X₀.toFormalODModule X₀.toFormalODModule
      (VersalAsm.map_fst_eq _) hF γ' hγ'
    rwa [VersalAsm.comp_comp_j] at this
  have hγbc : X₀.toFormalODModule.HasStructureConstants
      (fun i => MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i)) a := by
    have := VersalAsm.hasStructureConstants_reduce X₀.toFormalODModule X₀.toFormalODModule
      (VersalAsm.map_fst_eq _) hF γ' _ hcon
    simp only [VersalAsm.fst_algebraMap_add_smul_eps] at this
    exact this

  have hLie : IsCompl (X₀.toFormalODModule.lieZero j₀) (X₀.toFormalODModule.lieOne j₀) := X₀.isSpecial.1
  have W2 := fun i => CerednikDrinfeld.FormalODModule.exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
    j₀ X₀.toFormalODModule hLie _ hγb hF γ' hγ' (fun _ => rfl) i 3
  choose c g hg hexp hc0 hcm using W2
  have hc0' : ∀ i, c i 0 = 1 + TrivSqZeroExt.snd (c i 0) • DualNumber.eps := fun i => by
    conv_lhs => rw [VersalAsm.dualNumber_eq (c i 0)]
    rw [hc0 i 0 rfl, map_one]
  have hc1' : ∀ i, c i 1 = TrivSqZeroExt.snd (c i 1) • DualNumber.eps := fun i => by
    conv_lhs => rw [VersalAsm.dualNumber_eq (c i 1)]
    rw [hcm i 1 (by simp), map_zero, zero_add]
  have hc2' : ∀ i, c i 2 = TrivSqZeroExt.snd (c i 2) • DualNumber.eps := fun i => by
    conv_lhs => rw [VersalAsm.dualNumber_eq (c i 2)]
    rw [hcm i 2 (by simp), map_zero, zero_add]
  have hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F) (1 + TrivSqZeroExt.snd (c i 0) • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
            (MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i)) : MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F) (TrivSqZeroExt.snd (c i 1) • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
              (MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' (FormalODModule.piIndex 0 i))) :
                MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F) (TrivSqZeroExt.snd (c i 2) • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
              (MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i)) : MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F)))^[3] (g i) := by
    intro i
    conv_lhs => rw [hexp i]
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Function.iterate_zero, Function.iterate_one, id_eq,
      zero_add, VersalAsm.piIndex_one, VersalAsm.piIndex_three]
    rw [show FormalODModule.piIndex (1 + 1) i = FormalODModule.piIndex 0 i from VersalAsm.piIndex_two i,
      show FormalODModule.piIndex (2 + 1) i = i from VersalAsm.piIndex_three i,
      ← hc0' i, ← hc1' i, ← hc2' i]

  letI : Algebra ℤ_[q] k := ((ZMod.castHom (dvd_refl q) k).comp (PadicInt.toZMod (p := q))).toAlgebra
  have hV := MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt q X₀.F
  have hFV := CerednikDrinfeld.FormalODModule.exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
    X₀.toFormalODModule hV _ a hγbc i₀ ha0

  obtain ⟨h0f, h1f, h2f⟩ :=
    CerednikDrinfeld.FormalODModule.hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
      j₀ X₀.toFormalODModule _ hγb a hγbc γ' hγ' (fun i => TrivSqZeroExt.snd (c i 0)) (fun i => TrivSqZeroExt.snd (c i 1))
      (fun i => TrivSqZeroExt.snd (c i 2)) g hshape _ hcon

  set s := TrivSqZeroExt.snd (c i₀ 0) with hs_def
  set s' := TrivSqZeroExt.snd (c (FormalODModule.piIndex 0 i₀) 0) with hs'_def
  set vv := TrivSqZeroExt.snd (c i₀ 1) with hv_def
  have e0 := VersalAsm.eq_of_algebraMap_add_smul_eps_eq (h0f (FormalODModule.piIndex 0 i₀))
  have e1 := VersalAsm.eq_of_algebraMap_add_smul_eps_eq (h1f i₀)
  have e2 := VersalAsm.eq_of_algebraMap_add_smul_eps_eq (h1f (FormalODModule.piIndex 0 i₀))
  have h2' := h2f i₀ ha0 hFV
  rw [sub_eq_add_neg, ← neg_smul] at h2'
  have e3 := VersalAsm.eq_of_algebraMap_add_smul_eps_eq h2'
  simp only [VersalAsm.piIndex_zero_piIndex_zero, hne, and_false, and_true, ite_false, ite_true, true_and, false_and,
    eq_self_iff_true, one_ne_zero, zero_ne_one, Nat.zero_ne_one, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, ha0, ne_eq,
    zero_pow (Fact.out : q.Prime).ne_zero, zero_mul, mul_zero, sub_zero] at e0 e1 e2 e3

  have hss : TrivSqZeroExt.snd (c (FormalODModule.piIndex 0 i₀) 0) = TrivSqZeroExt.snd (c i₀ 0) := by
    have : (TrivSqZeroExt.snd (c (FormalODModule.piIndex 0 i₀) 0) - TrivSqZeroExt.snd (c i₀ 0)) *
        a 0 (FormalODModule.piIndex 0 i₀) = 0 := by
      exact e0.symm
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hu
  apply hδ (TrivSqZeroExt.snd (c i₀ 1)) (TrivSqZeroExt.snd (c i₀ 0))
  funext j
  fin_cases j
  · show δ 0 = _
    rw [e1]; simp; ring
  · show δ 1 = _
    rw [e2, hss]; simp; ring
  · show δ 2 = _
    rw [e3, hss]; simp; ring

end

end S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and (solution)
