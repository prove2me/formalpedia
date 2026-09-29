-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/36fb8b3d-413a-5bb4-b22a-f659604a32d5

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mOSW2

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem fst_comp_inl : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap k (DualNumber k)) = RingHom.id k := RingHom.ext fun a => TrivSqZeroExt.fst_inl k a

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

theorem map_fst_eq (X₀ : FormalODModule q k) : (X₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀ := by
  rw [FormalODModule.map_map, fst_comp_inl, FormalODModule.map_id]

theorem mem_gradedPiece_baseChangeEq (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (Y : FormalODModule q k) (hY : (X₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = Y)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = Y.F) (n : ℕ)
    {f : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F}
    (hf : f ∈ (X₀.map (algebraMap k (DualNumber k))).gradedPiece ((algebraMap k (DualNumber k)).comp j₀) n) :
    baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF f ∈ Y.gradedPiece (((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp j₀)) n := by
  subst hY
  exact FormalODModule.baseChange_mem_gradedPiece (TrivSqZeroExt.fstHom k k k).toRingHom (X₀.map (algebraMap k (DualNumber k))) ((algebraMap k (DualNumber k)).comp j₀) n hf

theorem comp_comp_j (j₀ : Zp2 q →+* k) : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp j₀) = j₀ := by
  rw [← RingHom.comp_assoc, fst_comp_inl, RingHom.id_comp]

theorem baseChangeEq_of_eq_id {d : ℕ} {Φ : MvFormalGroup d k} [Φ.IsComm] (φ : k →+* k) (hφ : φ = RingHom.id k)
    (h : Φ.map φ = Φ) (m : MvFormalGroup.CartierModule q Φ) : baseChangeEq φ h m = m := by
  subst hφ
  exact baseChangeEq_id h m

theorem baseChangeEq_baseChange_eq (X₀ : FormalODModule q k)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F) (m : MvFormalGroup.CartierModule q X₀.F) :
    baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (baseChange (algebraMap k (DualNumber k)) m) = m := by
  have h'' : X₀.F.map (((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap k (DualNumber k))) = X₀.F := by rw [fst_comp_inl, MvFormalGroup.map_ringHom_id]
  exact (baseChangeEq_baseChangeEq (algebraMap k (DualNumber k)) (TrivSqZeroExt.fstHom k k k).toRingHom rfl hF h'' m).trans
    (baseChangeEq_of_eq_id _ fst_comp_inl h'' m)

theorem dualNumber_eq (x : DualNumber k) : x = algebraMap k (DualNumber k) (TrivSqZeroExt.fst x) + TrivSqZeroExt.snd x • DualNumber.eps := by
  rw [← DualNumber.inr_eq_smul_eps]
  exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm

theorem triv_expansion {B : Type u} [CommRing B] [CharP B q] {X : FormalODModule q B}
    (γ : Fin 2 → MvFormalGroup.CartierModule q X.F) (i : Fin 2) (n : ℕ) :
    γ i = (∑ m : Fin (n + 1), (⇑(verschiebung (p := q) (Φ := X.F)))^[(m : ℕ)]
        (homothety ((fun m : Fin (n + 1) => if (m : ℕ) = 0 then (1 : B) else 0) m)
          (γ ⟨((i : ℕ) + m) % 2, Nat.mod_lt _ two_pos⟩))) +
      (⇑(verschiebung (p := q) (Φ := X.F)))^[n + 1] 0 := by
  rw [iterate_map_zero, add_zero, Fin.sum_univ_succ]
  have hi : (⟨((i : ℕ) + ((0 : Fin (n + 1)) : ℕ)) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = i := by
    ext
    simp only [Fin.val_zero, add_zero]
    exact Nat.mod_eq_of_lt i.isLt
  rw [hi]
  simp only [Fin.val_zero, if_true, Function.iterate_zero, id_eq, homothety_one]
  rw [Finset.sum_eq_zero, add_zero]
  intro m _
  rw [if_neg (by simp [Fin.val_succ]), homothety_zero_left, iterate_map_zero]

end P2mOSW2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq.P2mOSW2"

open P2mOSW2 CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (hLie : IsCompl (X₀.lieZero j₀) (X₀.lieOne j₀))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (hred : ∀ i, MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i) = γ i)
    (i : Fin 2) (N : ℕ) :
    ∃ (c : Fin N → DualNumber k) (g : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F),
      g ∈ (X₀.map (algebraMap k (DualNumber k))).gradedPiece ((algebraMap k (DualNumber k)).comp j₀) (i + N) ∧
      γ' i =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (MvFormalGroup.CartierModule.homothety (c m)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
              (γ (FormalODModule.piIndex ((m : ℕ) + 1) i))))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[N] g ∧
      (∀ m : Fin N, (m : ℕ) = 0 → TrivSqZeroExt.fst (c m) = 1) ∧
      (∀ m : Fin N, 1 ≤ (m : ℕ) → TrivSqZeroExt.fst (c m) = 0) := by
  classical
  have hγe : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀)
      (fun l => baseChange (algebraMap k (DualNumber k)) (γ l)) := hγ.map (algebraMap k (DualNumber k))
  have hLieε := (CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image q j₀ X₀ hLie
      (algebraMap k (DualNumber k))).1

  obtain ⟨⟨c, g⟩, ⟨hg, hexp⟩, -⟩ :=
    CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
      q ((algebraMap k (DualNumber k)).comp j₀) (X₀.map (algebraMap k (DualNumber k))) hLieε _ hγe i N (γ' i) (hγ'.1 i)
  have hidx : ∀ m : Fin N, (⟨((i : ℕ) + m) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = FormalODModule.piIndex ((m : ℕ) + 1) i := by
    intro m
    ext
    simp only [FormalODModule.piIndex_val]
    omega
  have hV : (⇑(verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)) :
      MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F → _) =
      ⇑(verschiebung (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)) :=
    congrArg DFunLike.coe (verschiebungInt_eq_verschiebung (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F))
  refine ⟨c, g, hg, ?_, ?_⟩
  · rw [hV]
    simp only [← hidx]
    exact hexp

  have hred' := congrArg (baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF) hexp
  rw [hred i, map_add, map_sum] at hred'
  simp only [baseChangeEq_verschiebung_iterate, baseChangeEq_homothety, baseChangeEq_baseChange_eq] at hred'
  have hgb : baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF g ∈ X₀.gradedPiece j₀ ((i : ℕ) + N) := by
    have := mem_gradedPiece_baseChangeEq j₀ X₀ X₀ (map_fst_eq X₀) hF ((i : ℕ) + N) hg
    rwa [comp_comp_j] at this
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨fun m => m.elim0, fun m => m.elim0⟩
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have huniq := (CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
      q j₀ X₀ hLie γ hγ i (n + 1) (γ i) (hγ.1 i)).unique
      (y₁ := (fun m => TrivSqZeroExt.fst (c m), baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF g))
      (y₂ := (fun m : Fin (n + 1) => if (m : ℕ) = 0 then (1 : k) else 0, 0))
      ⟨hgb, hred'⟩ ⟨(X₀.gradedPiece j₀ _).zero_mem, triv_expansion γ i n⟩
    have hc : ∀ m : Fin (n + 1), TrivSqZeroExt.fst (c m) = if (m : ℕ) = 0 then 1 else 0 :=
      fun m => congrFun (congrArg Prod.fst huniq) m
    refine ⟨fun m hm => by rw [hc, if_pos hm], fun m hm => by rw [hc, if_neg (by omega)]⟩

end
end S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq (solution)
