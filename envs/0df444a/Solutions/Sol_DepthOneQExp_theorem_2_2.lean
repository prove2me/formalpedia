-- Prove2me | solution 1 for DepthOneQExp.theorem_2_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:17:41.993796+00:00
-- url     : https://prove2.me/submissions/7df8bf00-1b2c-434c-a560-cff89de280b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_DepthOneQExp_xGate
import Definitions.Def_DepthOneQExp_zGate
import Definitions.Def_DepthOneQExp_cnotGate
import Definitions.Def_DepthOneQExp_U
import Definitions.Def_DepthOneQExp_IsQuantumExpanderGap
import Definitions.Def_DepthOneQExp_cnotU
import Definitions.Def_ConstGapCircuits_spectralGap
import Theorems.Thm_DepthOneQExp_theorem_2_3
import Theorems.Thm_DepthOneQExp_theorem_2_13
import Theorems.Thm_DepthOneQExp_U_mem_depthOneSet

open scoped Matrix.Norms.L2Operator Kronecker
open Matrix DepthOneQExp

theorem reindex_l2_norm_aux {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) : ‖Matrix.reindex e e A‖ = ‖A‖ := by
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have h : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.reindex e e A) =
      (L : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ n).comp
        ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A).comp
          (L.symm : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m)) := by
    ext v j
    simp [L, Matrix.mulVec, dotProduct, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]
    exact (Equiv.sum_comp e _).symm.trans (by simp)
  rw [← Matrix.l2_opNorm_toEuclideanCLM, h, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, Matrix.l2_opNorm_toEuclideanCLM]

noncomputable def permToMatrixHom (α : Type) [Fintype α] [DecidableEq α] :
    Equiv.Perm α →* Matrix α α ℂ where
  toFun := permToMatrix
  map_one' := permToMatrix_one
  map_mul' := permToMatrix_mul

theorem permToMatrix_list_prod {α : Type} [Fintype α] [DecidableEq α] (l : List (Equiv.Perm α)) :
    permToMatrix l.prod = (l.map permToMatrix).prod :=
  map_list_prod (permToMatrixHom α) l

theorem cnotU_eq (s : ℕ) (k : Fin 14) :
    permToMatrix ((cnotU s k : cnotGroup (3 * s)) : Equiv.Perm (MITMSynthesis.Q (3 * s))) =
      U s (Fin.natAdd 2 k) := by
  unfold cnotU U
  dsimp only
  fin_cases k <;> simp only [Fin.natAdd_mk, Fin.reduceFinMk, Matrix.cons_val, Nat.reduceAdd]
  all_goals first
    | rfl
    | (simp only [SubmonoidClass.coe_list_prod, permToMatrix_list_prod, List.map_map]; rfl)

theorem U_unitary (s : ℕ) (i : Fin 16) :
    U s i ∈ Matrix.unitaryGroup (MITMSynthesis.Q (3 * s)) ℂ := by
  refine Fin.addCases (m := 2) (n := 14) (motive := fun i =>
    U s i ∈ Matrix.unitaryGroup (MITMSynthesis.Q (3 * s)) ℂ) (fun j => ?_) (fun k => ?_) i
  · fin_cases j
    · exact permToMatrix_mem_unitaryGroup _
    · exact zMat_mem_unitaryGroup _ _
  · rw [← cnotU_eq]
    exact permToMatrix_mem_unitaryGroup _


noncomputable def diagPerm (α : Type) : Equiv.Perm α →* Equiv.Perm (α × α) where
  toFun σ := Equiv.prodCongr σ σ
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

noncomputable def unitaryPermHom (β : Type) [Fintype β] [DecidableEq β] :
    Equiv.Perm β →* Matrix.unitaryGroup β ℂ :=
  (permToMatrixHom β).codRestrict (Matrix.unitaryGroup β ℂ) (fun σ => permToMatrix_mem_unitaryGroup σ)

noncomputable def tensorHom (n : ℕ) :
    cnotGroup n →* Matrix.unitaryGroup (Fin (Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n))) ℂ :=
  (unitaryPermHom (Fin (Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n)))).comp
    (((Equiv.permCongrHom (Fintype.equivFin (MITMSynthesis.Q n × MITMSynthesis.Q n))).toMonoidHom.comp
      (diagPerm _)).comp (cnotGroup n).subtype)

noncomputable abbrev tensorRep (n : ℕ) : ConstGapCircuits.UnitaryRep (cnotGroup n) :=
  ⟨Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n), tensorHom n, continuous_of_discreteTopology⟩

theorem tensorHom_apply (n : ℕ) (g : cnotGroup n) :
    ((tensorHom n g : Matrix.unitaryGroup (Fin (Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n))) ℂ) :
      Matrix (Fin (Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n)))
        (Fin (Fintype.card (MITMSynthesis.Q n × MITMSynthesis.Q n))) ℂ) =
      Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
        (permToMatrix (g : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ
          permToMatrix (g : Equiv.Perm (MITMSynthesis.Q n))) := by
  ext i j
  show permToMatrix ((Fintype.equivFin (MITMSynthesis.Q n × MITMSynthesis.Q n)).permCongr
      (Equiv.prodCongr (g : Equiv.Perm (MITMSynthesis.Q n)) g)) i j = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  unfold permToMatrix
  set e := Fintype.equivFin (MITMSynthesis.Q n × MITMSynthesis.Q n)
  obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, d⟩, rfl⟩ := e.surjective j
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
    e.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h1 : a = (g : Equiv.Perm _) c <;> by_cases h2 : b = (g : Equiv.Perm _) d <;> simp [h1, h2]

theorem tensorRep_hom (n : ℕ) (g : cnotGroup n) :
    ((tensorRep n).hom g : Matrix (Fin (tensorRep n).dim) (Fin (tensorRep n).dim) ℂ) =
      Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
        (permToMatrix (g : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ
          permToMatrix (g : Equiv.Perm (MITMSynthesis.Q n))) :=
  tensorHom_apply n g

theorem isQuantumExpanderGap_U (s : ℕ) (hs : 1 ≤ s) :
    IsQuantumExpanderGap (U s) (1 / (2 * 10 ^ 8)) := by
  have hn : 2 ≤ 3 * s := by omega
  set ε : ℝ := 1 / (48 * 10 ^ 5) with hε
  -- Theorem 2.3 applied to the representation `P ↦ P ⊗ P`
  have h23 := theorem_2_3 s hs (tensorRep (3 * s))
  set e := Fintype.equivFin (MITMSynthesis.Q (3 * s) × MITMSynthesis.Q (3 * s))
  set X : Matrix (MITMSynthesis.Q (3 * s) × MITMSynthesis.Q (3 * s))
      (MITMSynthesis.Q (3 * s) × MITMSynthesis.Q (3 * s)) ℂ :=
    (1 / ((14 : ℕ) : ℂ)) • ∑ i, (permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s))) ⊗ₖ
        permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s)))) - cnotAvg (3 * s) with hX
  have hP : ‖X‖ ≤ 1 - ε := by
    rw [← reindex_l2_norm_aux e X, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine le_of_eq_of_le ?_ h23
    unfold ConstGapCircuits.opNorm
    congr 2
    ext i j
    simp only [tensorRep_hom, tensorHom_apply, hX, cnotAvg, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    push_cast
    ring
  have h213 := theorem_2_13 (3 * s) hn 14 (cnotU s) ε hP
  -- monotonicity in the gap and reordering of the family
  unfold IsQuantumExpanderGap at h213 ⊢
  have hgap : (1 : ℝ) - min ((14 : ℕ) * ε) 2 / (24 * ((14 : ℕ) + 2)) ≤ 1 - 1 / (2 * 10 ^ 8) := by
    rw [hε]; norm_num
  refine le_trans (le_of_eq ?_) (h213.trans hgap)
  have hU : ∀ i : Fin 16, U s i = Fin.append
      (fun i => permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s))))
      ![permToMatrix (xPerm (3 * s) 0), zMat (3 * s) 0] (finAddFlip (m := 2) (n := 14) i) := by
    intro i
    refine Fin.addCases (m := 2) (n := 14) (motive := fun i => U s i = Fin.append
      (fun i => permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s))))
      ![permToMatrix (xPerm (3 * s) 0), zMat (3 * s) 0] (finAddFlip (m := 2) (n := 14) i))
      (fun j => ?_) (fun k => ?_) i
    · rw [finAddFlip_apply_castAdd, Fin.append_right]
      fin_cases j <;> rfl
    · rw [finAddFlip_apply_natAdd, Fin.append_left, cnotU_eq]
  congr 2
  simp_rw [hU]
  congr 1
  exact Equiv.sum_comp (finAddFlip (m := 2) (n := 14)) (fun j => Fin.append
      (fun i => permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s))))
    ![permToMatrix (xPerm (3 * s) 0), zMat (3 * s) 0] j ⊗ₖ (Fin.append
    (fun i => permToMatrix (cnotU s i : Equiv.Perm (MITMSynthesis.Q (3 * s))))
    ![permToMatrix (xPerm (3 * s) 0), zMat (3 * s) 0] j).map star)

theorem solution (s : ℕ) (hs : 1 ≤ s) :
    (∀ i, U s i ∈ Matrix.unitaryGroup (MITMSynthesis.Q (3 * s)) ℂ) ∧
    IsQuantumExpanderGap (U s) (1 / (2 * 10 ^ 8)) ∧
    (∀ i, U s i ∈ MITMSynthesis.depthOneSet (3 * s) {xGate, zGate, cnotGate}) :=
  ⟨U_unitary s, isQuantumExpanderGap_U s hs, U_mem_depthOneSet s hs⟩
