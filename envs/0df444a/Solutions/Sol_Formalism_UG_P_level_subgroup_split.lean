-- Prove2me | solution 1 for Formalism.UG.P.level_subgroup_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:55.720067+00:00
-- url     : https://prove2.me/submissions/469dc028-1fe9-4e5e-8b1d-19cc9fb70cbc

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Theorems.Thm_Formalism_UG_P_levelvsplit_coe_bc
import Theorems.Thm_Formalism_UG_P_levelvsplit_mem_range_iff
import Theorems.Thm_Formalism_UG_P_levelvsplit_unitary
import Theorems.Thm_Formalism_UG_P_levelvsplit_solve
import Theorems.Thm_Formalism_UG_P_levelvsplit_int_mul
import Theorems.Thm_Formalism_UG_P_stabilizer_standard_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.LevelVSplit := by
  intro F E _ _ _ _ _ n _ _ σ J v φ hσ hS hu g hg
  obtain ⟨u, huO, huA⟩ := hu
  have hOr : ∀ x : v.adicCompletion F,
      x ∈ Set.range (v.adicCompletionIntegers F).toSubring.subtype ↔
        x ∈ v.adicCompletionIntegers F :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hSr : ∀ x, x ∈ Set.range (algebraMap
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (E ⊗[F] v.adicCompletion F)) ↔
        x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hinjS : Function.Injective (algebraMap
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (E ⊗[F] v.adicCompletion F)) := Subtype.val_injective
  have hinjO : Function.Injective (v.adicCompletionIntegers F).toSubring.subtype :=
    Subtype.val_injective
  rw [GLint, levelvsplit_mem_range_iff _ hinjO] at huO ⊢
  simp only [hOr] at huO ⊢
  obtain ⟨huO1, huO2⟩ := huO
  have hstab : g ∈ levelV σ J v ↔ g ∈ stabGL (stdLat (n := n)
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) :=
    ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  rw [hstab, stabilizer_standard_lattice _ _ _ hinjS, levelvsplit_mem_range_iff _ hinjS]
  simp only [hSr, hS]
  rw [← map_inv, levelvsplit_coe_bc, levelvsplit_coe_bc]
  have hJu : (J.map (inclE (F := F) (v.adicCompletion F))).map
      ((RingHom.fst _ _).comp φ.toRingHom) = (u : Matrix n n (v.adicCompletion F)) := by
    rw [huA]; ext i j; rfl
  have rel1 := levelvsplit_unitary _ φ hσ _ g hg
  have rel2 := levelvsplit_unitary _ φ hσ _ g⁻¹ (inv_mem hg)
  rw [hJu] at rel1 rel2
  have hg1 : (g : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) *
      ((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : ((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) *
      (g : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : (u : Matrix n n (v.adicCompletion F)) * ((u⁻¹ : GL n _) : Matrix n n _) = 1 :=
    u.mul_inv
  have s1 := levelvsplit_solve _ _ _ _ _ hA hg1 rel1
  have s2 := levelvsplit_solve _ _ _ _ _ hA hg2 rel2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · have e := congrFun (congrFun s1 i) j
      have hint := levelvsplit_int_mul _ _ _
        (levelvsplit_int_mul _ _ _ huO1 (fun a b => h2 a b)) huO2 j i
      have : ((g : Matrix n n _).map ((RingHom.snd _ _).comp φ.toRingHom)) i j ∈
          v.adicCompletionIntegers F := by
        rw [e]; exact hint
      exact this
    · have e := congrFun (congrFun s2 i) j
      have hint := levelvsplit_int_mul _ _ _
        (levelvsplit_int_mul _ _ _ huO1 (fun a b => h1 a b)) huO2 j i
      have : (((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.snd _ _).comp φ.toRingHom)) i j ∈
          v.adicCompletionIntegers F := by
        rw [e]; exact hint
      exact this
end Formalism.UG.P
