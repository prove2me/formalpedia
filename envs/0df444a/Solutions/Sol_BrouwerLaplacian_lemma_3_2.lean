-- Prove2me | solution 1 for BrouwerLaplacian.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:23.670193+00:00
-- url     : https://prove2.me/submissions/4ff34a22-20c9-4e36-b730-8b4c8e5e7bd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_BrouwerLaplacian_splitGraphOf
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_BrouwerLaplacian_conjDeg
import Definitions.Def_BrouwerLaplacian_IsSplitWith
import Theorems.Thm_BrouwerLaplacian_theorem_1_2_grone_merris_bai

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

theorem cent_apply {n : ℕ} (i j : Fin n) :
    centering n i j = (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  simp [centering, onesMat, Matrix.one_apply]

theorem cent_symm {n : ℕ} (i j : Fin n) : centering n j i = centering n i j := by
  rw [cent_apply, cent_apply]; simp [eq_comm]

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.E53

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.E53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.Reflect

open Finset Matrix BrouwerLaplacian

/-- the Householder reflection `H = 1 - (2/(w⬝w)) w wᵀ` -/
noncomputable def hh {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 / (w ⬝ᵥ w)) • vecMulVec w w

theorem hh_symm {n : ℕ} (w : Fin n → ℝ) : (hh w)ᵀ = hh w := by
  ext i j
  simp [hh, Matrix.transpose_apply, Matrix.one_apply, vecMulVec_apply, eq_comm, mul_comm]

theorem vv_sq {n : ℕ} (w : Fin n → ℝ) :
    vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem hh_mul_self {n : ℕ} (w : Fin n → ℝ) (hw : w ⬝ᵥ w ≠ 0) : hh w * hh w = 1 := by
  unfold hh
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vv_sq]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  field_simp
  ring

theorem hh_mulVec {n : ℕ} (w x : Fin n → ℝ) :
    hh w *ᵥ x = x - ((2 / (w ⬝ᵥ w)) * (w ⬝ᵥ x)) • w := by
  simp only [hh, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_assoc]

theorem hh_mul_of_mulVec_zero {n : ℕ} (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) (hw : A *ᵥ w = 0) : hh w * A = A ∧ A * hh w = A := by
  constructor
  · unfold hh
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul]
    have : w ᵥ* A = 0 := by
      have := Matrix.vecMul_transpose A w
      rw [hA] at this; rw [this]; exact hw
    simp [this]
  · unfold hh
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec, hw]
    simp

theorem exists_H {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = L) (z u : Fin n → ℝ)
    (hz : z ⬝ᵥ z = 1) (hu : u ⬝ᵥ u = 1) (hLz : L *ᵥ z = 0) (hLu : L *ᵥ u = 0) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, Hᵀ = H ∧ H * H = 1 ∧ H *ᵥ u = z ∧ H * L = L ∧ L * H = L := by
  by_cases hw : (z - u) ⬝ᵥ (z - u) = 0
  · have : z = u := sub_eq_zero.1 ((dotProduct_self_eq_zero (v := z - u)).1 hw)
    subst this
    exact ⟨1, by simp, by simp, by simp, by simp, by simp⟩
  set w := z - u with hwdef
  have hLw : L *ᵥ w = 0 := by rw [hwdef, Matrix.mulVec_sub, hLz, hLu, sub_zero]
  obtain ⟨hHL, hLH⟩ := hh_mul_of_mulVec_zero w L hL hLw
  refine ⟨hh w, hh_symm w, hh_mul_self w hw, ?_, hHL, hLH⟩
  rw [hh_mulVec]
  have h1 : w ⬝ᵥ u = z ⬝ᵥ u - 1 := by rw [hwdef, sub_dotProduct, hu]
  have h2 : w ⬝ᵥ w = 2 - 2 * (z ⬝ᵥ u) := by
    rw [hwdef, dotProduct_sub, sub_dotProduct, sub_dotProduct, hz, hu, dotProduct_comm u z]; ring
  have h4 : (2 - 2 * (z ⬝ᵥ u)) ≠ 0 := by rw [← h2]; exact hw
  have h3 : (2 / (w ⬝ᵥ w)) * (w ⬝ᵥ u) = -1 := by
    have h5 : 1 - z ⬝ᵥ u ≠ 0 := fun h => h4 (by linarith)
    rw [h1, h2]
    field_simp
    ring
  rw [h3, hwdef]; ext i; simp

end BrouwerLaplacian.Dev.Reflect
end

section
namespace BrouwerLaplacian.Dev.TopK

open Finset Matrix BrouwerLaplacian

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- the eigenvalues, sorted decreasingly -/
noncomputable def ev (hA : A.IsHermitian) : Fin (Fintype.card (Fin n)) → ℝ := hA.eigenvalues₀

/-- eigenvector -/
noncomputable def bv (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin n))) : Fin n → ℝ :=
  ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace i).ofLp

theorem bv_dot (hA : A.IsHermitian) (i j : Fin (Fintype.card (Fin n))) :
    bv hA i ⬝ᵥ bv hA j = if i = j then 1 else 0 := by
  have := orthonormal_iff_ite.1
    ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [bv, dotProduct_comm] using this

theorem mulVec_bv (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin n))) :
    A *ᵥ bv hA i = ev hA i • bv hA i := by
  have := (isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i
  have h2 := congrArg WithLp.ofLp this
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply] at h2
  exact h2

end BrouwerLaplacian.Dev.TopK
end

section
namespace BrouwerLaplacian.Dev.L51a

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.L51a
end

section
namespace BrouwerLaplacian.Dev.L51

open Finset Matrix BrouwerLaplacian

theorem lap_ev_last {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n)
    (j : Fin (Fintype.card (Fin n))) (hj : j.val + 1 = Fintype.card (Fin n)) :
    TopK.ev (G.isHermitian_lapMatrix ℝ) j = 0 := by
  set hA := G.isHermitian_lapMatrix ℝ with hAdef
  have hpsd := G.posSemidef_lapMatrix ℝ
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hnn : ∀ i : Fin (Fintype.card (Fin n)), 0 ≤ TopK.ev hA i := by
    intro i
    have := hpsd.eigenvalues_nonneg (e i)
    simpa [Matrix.IsHermitian.eigenvalues, TopK.ev, e] using this
  have hex : ∃ i : Fin (Fintype.card (Fin n)), TopK.ev hA i = 0 := by
    have hdet : (G.lapMatrix ℝ).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun _ => 1, ?_, G.lapMatrix_mulVec_const_eq_zero⟩
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    rw [hA.det_eq_prod_eigenvalues] at hdet
    simp only [RCLike.ofReal_real_eq_id, id] at hdet
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hdet
    refine ⟨e.symm i, ?_⟩
    simpa [Matrix.IsHermitian.eigenvalues, TopK.ev, e] using hi
  obtain ⟨i, hi⟩ := hex
  have hle : TopK.ev hA j ≤ TopK.ev hA i := by
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_def]; omega
  linarith [hnn j]

end BrouwerLaplacian.Dev.L51

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.NucSym

open Matrix Polynomial Finset WainwrightHDS.NucNorm

theorem charpoly_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A * A).charpoly = ∏ i, (X - C ((hA.eigenvalues i) ^ 2)) := by
  have h1 : A * A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [map_mul, ← hA.spectral_theorem]
  conv_lhs => rw [h1, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal, diagonal_mul_diagonal, sq]

theorem eig_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} {S S' : E →ₗ[ℝ] E} (h : S = S') (hS : S.IsSymmetric) (hS' : S'.IsSymmetric)
    (hm : Module.finrank ℝ E = m) : hS.eigenvalues hm = hS'.eigenvalues hm := by
  subst h; rfl

theorem multiset_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hA2 : (A * A).IsHermitian) :
    (univ : Finset (Fin n)).val.map hA2.eigenvalues
      = (univ : Finset (Fin n)).val.map (fun i => (hA.eigenvalues i) ^ 2) := by
  have h1 := hA2.roots_charpoly_eq_eigenvalues
  rw [charpoly_sq hA, Polynomial.roots_prod] at h1
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h1
    rw [h1]
    simp [Function.comp_def]
  · exact Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero _

theorem nuc_eq_sum_abs {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    nucNorm A = ∑ i, |hA.eigenvalues i| := by
  have hA2 : (A * A).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self A
    rwa [hA.eq] at this
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A = Matrix.toEuclideanLin (A * A) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA.eq]
    exact (Matrix.toLpLin_mul 2 2 2 A A).symm
  have hsv : ∀ i : Fin (Fintype.card (Fin n)),
      (Matrix.toEuclideanLin A).singularValues i = √(hA2.eigenvalues₀ i) := by
    intro i
    rw [(Matrix.toEuclideanLin A).singularValues_fin hn i]
    congr 1
    exact eig_congr hadj _ _ hn ▸ rfl
  unfold nucNorm singVal
  rw [min_self, show Finset.range n = Finset.range (Fintype.card (Fin n)) from by
    rw [Fintype.card_fin], Finset.sum_range]
  simp only [hsv]
  rw [← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm.sum_comp]
  have hm := multiset_sq hA hA2
  have key : ∀ i : Fin n, √(hA2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm i))
      = √(hA2.eigenvalues i) := fun i => rfl
  simp only [key]
  show (Multiset.map (fun i => √(hA2.eigenvalues i)) univ.val).sum
    = (Multiset.map (fun i => |hA.eigenvalues i|) univ.val).sum
  have h2 : (fun i => √(hA2.eigenvalues i)) = (fun x => √x) ∘ hA2.eigenvalues := rfl
  rw [h2, ← Multiset.map_map, hm, Multiset.map_map]
  congr 2
  funext i
  simp [Real.sqrt_sq_eq_abs]

end BrouwerLaplacian.Dev.NucSym
end

section
namespace BrouwerLaplacian.Dev.Spec32

open Finset Matrix Polynomial BrouwerLaplacian

theorem abs_sum_of_charpoly {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (d : Fin n → ℝ) (hch : B.charpoly = ∏ i, (X - C (d i))) :
    ∑ i, |hB.eigenvalues i| = ∑ i, |d i| := by
  have h1 := hB.roots_charpoly_eq_eigenvalues
  rw [hch, Polynomial.roots_prod] at h1
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h1
    have h2 : (univ : Finset (Fin n)).val.map hB.eigenvalues
        = (univ : Finset (Fin n)).val.map d := by
      rw [h1]; simp [Function.comp_def]
    have h3 : ∑ i, |hB.eigenvalues i| = (((univ : Finset (Fin n)).val.map hB.eigenvalues).map (fun x => |x|)).sum := by
      rw [Multiset.map_map]; rfl
    have h4 : ∑ i, |d i| = (((univ : Finset (Fin n)).val.map d).map (fun x => |x|)).sum := by
      rw [Multiset.map_map]; rfl
    rw [h3, h4, h2]
  · exact Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero _

theorem charpoly_spec {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsHermitian) (r : ℝ)
    (is : Fin n) :
    (L - r • (1 : Matrix (Fin n) (Fin n) ℝ)
      + r • vecMulVec (⇑(hL.eigenvectorBasis is)) (⇑(hL.eigenvectorBasis is))).charpoly
      = ∏ i, (X - C (hL.eigenvalues i - r + (if i = is then r else 0))) := by
  set U := hL.eigenvectorUnitary with hU
  have hspec : L = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal (fun i => hL.eigenvalues i)
      * star (U : Matrix (Fin n) (Fin n) ℝ) := by
    have := hL.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa using this
  have hz : vecMulVec (⇑(hL.eigenvectorBasis is)) (⇑(hL.eigenvectorBasis is))
      = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal (fun i => if i = is then (1 : ℝ) else 0)
        * star (U : Matrix (Fin n) (Fin n) ℝ) := by
    ext a b
    simp [vecMulVec_apply, Matrix.mul_apply, Matrix.diagonal_apply, hU,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have h1 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have h2 : star (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hd : L - r • (1 : Matrix (Fin n) (Fin n) ℝ)
      + r • vecMulVec (⇑(hL.eigenvectorBasis is)) (⇑(hL.eigenvectorBasis is))
      = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal (fun i => hL.eigenvalues i - r
          + (if i = is then r else 0)) * star (U : Matrix (Fin n) (Fin n) ℝ) := by
    have hdiag : (diagonal (fun i => hL.eigenvalues i - r + (if i = is then r else 0)) :
        Matrix (Fin n) (Fin n) ℝ)
        = diagonal (fun i => hL.eigenvalues i) - r • (1 : Matrix (Fin n) (Fin n) ℝ)
          + r • diagonal (fun i => if i = is then (1 : ℝ) else 0) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.diagonal_apply, hab, Matrix.one_apply]
    rw [hdiag, hz]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, h1]
  rw [hd, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp [charpoly_diagonal]

theorem herm_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℝ) :
    (G.lapMatrix ℝ - r • centering n).IsHermitian := by
  have hC' : (r • centering n).IsHermitian := by
    ext i j; simp [Matrix.conjTranspose_apply, NLem.cent_symm i j]
  exact (G.isHermitian_lapMatrix ℝ).sub hC'

theorem cent_eq {n : ℕ} (hn : 1 ≤ n) :
    centering n = 1 - vecMulVec (fun _ : Fin n => 1 / Real.sqrt n) (fun _ => 1 / Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  ext i j
  simp [NLem.cent_apply, vecMulVec_apply, Matrix.one_apply]
  rw [← mul_inv, Real.mul_self_sqrt hnR.le]

theorem nuc_lap_sub {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n) (r : ℝ) :
    WainwrightHDS.NucNorm.nucNorm (G.lapMatrix ℝ - r • centering n) + |r|
      = ∑ j : Fin (Fintype.card (Fin n)), |(G.isHermitian_lapMatrix ℝ).eigenvalues₀ j - r| := by
  set hL := G.isHermitian_lapMatrix ℝ with hLdef
  set L := G.lapMatrix ℝ with hLd
  have hm : 1 ≤ Fintype.card (Fin n) := by simpa using hn
  let idx : Fin (Fintype.card (Fin n)) := ⟨Fintype.card (Fin n) - 1, by omega⟩
  have hidx : idx.val + 1 = Fintype.card (Fin n) := by simp [idx]; omega
  have hev : hL.eigenvalues₀ idx = 0 := L51.lap_ev_last G hn idx hidx
  set σ := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) with hσ
  set is : Fin n := σ idx with his
  have hzv : (⇑(hL.eigenvectorBasis is) : Fin n → ℝ) = TopK.bv hL idx := by
    simp [Matrix.IsHermitian.eigenvectorBasis, TopK.bv, his, hσ]
  set z : Fin n → ℝ := TopK.bv hL idx with hz
  have hzz : z ⬝ᵥ z = 1 := by rw [hz, TopK.bv_dot]; simp
  have hLz : L *ᵥ z = 0 := by
    rw [hz, TopK.mulVec_bv]
    have : TopK.ev hL idx = 0 := hev
    rw [this]; simp
  set c : ℝ := 1 / Real.sqrt n with hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set u : Fin n → ℝ := fun _ => c with hu
  have huu : u ⬝ᵥ u = 1 := by
    simp [hu, dotProduct, hc]
    field_simp
    exact (Real.sq_sqrt hnR.le).symm
  have hLu : L *ᵥ u = 0 := by
    have : u = c • (fun _ : Fin n => (1 : ℝ)) := by ext; simp [hu]
    rw [this, Matrix.mulVec_smul, G.lapMatrix_mulVec_const_eq_zero, smul_zero]
  have hLt : Lᵀ = L := G.isSymm_lapMatrix ℝ
  obtain ⟨H0, hH0s, hH0H0, hH0u, hH0L, hLH0⟩ := Reflect.exists_H L hLt z u hzz huu hLz hLu
  have hCu : centering n = 1 - vecMulVec u u := cent_eq hn
  have hHCH : H0 * centering n * H0 = 1 - vecMulVec z z := by
    rw [hCu, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hH0H0, mul_vecMulVec, vecMulVec_mul]
    have : u ᵥ* H0 = z := by
      have := Matrix.vecMul_transpose H0 u
      rw [hH0s] at this
      rw [this, hH0u]
    rw [this, hH0u]
  have hA' : H0 * (L - r • centering n) * H0 = L - r • (1 : Matrix (Fin n) (Fin n) ℝ)
      + r • vecMulVec z z := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hHCH,
      Matrix.mul_assoc, hLH0, hH0L]
    rw [smul_sub]; abel
  have hch : (L - r • centering n).charpoly
      = ∏ i, (X - C (hL.eigenvalues i - r + (if i = is then r else 0))) := by
    have := charpoly_spec hL r is
    rw [hzv] at this
    have e : (H0 * (L - r • centering n) * H0).charpoly = (L - r • centering n).charpoly := by
      rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hH0H0, Matrix.mul_one]
    rw [← this, ← hA', e]
  have hAh := herm_A G r
  have hd0 : hL.eigenvalues is = 0 := by
    have : hL.eigenvalues is = hL.eigenvalues₀ idx := by
      simp [Matrix.IsHermitian.eigenvalues, his, hσ]
    rw [this, hev]
  rw [NucSym.nuc_eq_sum_abs hAh, abs_sum_of_charpoly hAh _ hch]
  have hre : ∑ j : Fin (Fintype.card (Fin n)), |hL.eigenvalues₀ j - r|
      = ∑ i : Fin n, |hL.eigenvalues i - r| := by
    rw [← σ.symm.sum_comp]
    exact sum_congr rfl fun i _ => rfl
  rw [hre]
  have hpt : ∀ i : Fin n, |hL.eigenvalues i - r + (if i = is then r else 0)|
      + (if i = is then |r| else 0) = |hL.eigenvalues i - r| := by
    intro i
    by_cases hi : i = is
    · subst hi; simp [hd0]
    · simp [hi]
  have hs : ∑ i : Fin n, (if i = is then |r| else 0) = |r| := by
    simp [sum_ite_eq']
  rw [← hs, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => hpt i

end BrouwerLaplacian.Dev.Spec32
end

section
namespace BrouwerLaplacian.Dev.Split32

open Finset

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

theorem conj_sum (k : ℕ) :
    ∑ j ∈ Icc 1 k, (BrouwerLaplacian.conjDeg H j : ℝ) = ((∑ v, min (H.degree v) k : ℕ) : ℝ) := by
  have h1 : ∀ j, BrouwerLaplacian.conjDeg H j = ∑ v, if j ≤ H.degree v then 1 else 0 := by
    intro j; unfold BrouwerLaplacian.conjDeg; rw [Finset.card_filter]
  have h2 : ∀ v, ((Icc 1 k).filter (fun j => j ≤ H.degree v)).card = min (H.degree v) k := by
    intro v
    have : (Icc 1 k).filter (fun j => j ≤ H.degree v) = Icc 1 (min (H.degree v) k) := by
      ext j; simp only [mem_filter, mem_Icc]; omega
    rw [this]; simp
  have : ∑ j ∈ Icc 1 k, BrouwerLaplacian.conjDeg H j = ∑ v, min (H.degree v) k := by
    simp only [h1]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one, h2]
  rw [← this]; push_cast; rfl

theorem min_sum_le (K : Finset (Fin n)) (k : ℕ) :
    ∑ v, min (H.degree v) k ≤ #K * k + ∑ v ∈ Kᶜ, H.degree v := by
  rw [← sum_add_sum_compl K]
  refine add_le_add ?_ (sum_le_sum fun v _ => min_le_left _ _)
  calc ∑ v ∈ K, min (H.degree v) k ≤ ∑ v ∈ K, k := sum_le_sum fun v _ => min_le_right _ _
    _ = #K * k := by simp

theorem deg_sum (K : Finset (Fin n)) (hH : BrouwerLaplacian.IsSplitWith H K) :
    ∑ v, (H.degree v : ℝ)
      = (#K : ℝ) * ((#K : ℝ) - 1) + 2 * ∑ v ∈ Kᶜ, (H.degree v : ℝ) := by
  set a : Fin n → Fin n → ℝ := fun v u => if H.Adj v u then (1 : ℝ) else 0 with ha
  have hdeg : ∀ v, (H.degree v : ℝ) = ∑ u, a v u := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp [ha, sum_boole]
  have hsplit : ∀ v, (H.degree v : ℝ) = ∑ u ∈ K, a v u + ∑ u ∈ Kᶜ, a v u := fun v => by
    rw [hdeg v, sum_add_sum_compl]
  have hKK : ∀ v ∈ K, ∑ u ∈ K, a v u = (#K : ℝ) - 1 := by
    intro v hv
    have : ∀ u ∈ K, a v u = 1 - (if v = u then 1 else 0) := by
      intro u hu
      by_cases h : v = u
      · subst h; simp [ha]
      · have := hH.1 (by simpa using hv) (by simpa using hu) h
        simp [ha, this, h]
    rw [sum_congr rfl this, sum_sub_distrib]
    simp [hv]
  have hCC : ∀ v ∈ Kᶜ, ∑ u ∈ Kᶜ, a v u = 0 := by
    intro v hv
    refine sum_eq_zero fun u hu => ?_
    by_cases h : v = u
    · subst h; simp [ha]
    · have := hH.2 (by simpa using hv) (by simpa using hu) h
      simp [ha, this]
  have has : ∀ v u, a v u = a u v := fun v u => by simp only [ha, H.adj_comm v u]
  have hE : ∑ v ∈ Kᶜ, (H.degree v : ℝ) = ∑ u ∈ Kᶜ, ∑ v ∈ K, a u v := by
    refine sum_congr rfl fun v hv => ?_
    rw [hsplit, hCC v hv, add_zero]
  have hcross : ∑ v ∈ K, ∑ u ∈ Kᶜ, a v u = ∑ v ∈ Kᶜ, (H.degree v : ℝ) := by
    rw [hE, sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => has v u
  have hKsum : ∑ v ∈ K, (H.degree v : ℝ) = (#K : ℝ) * ((#K : ℝ) - 1)
      + ∑ v ∈ Kᶜ, (H.degree v : ℝ) := by
    have : ∀ v ∈ K, (H.degree v : ℝ) = ((#K : ℝ) - 1) + ∑ u ∈ Kᶜ, a v u := by
      intro v hv; rw [hsplit, hKK v hv]
    rw [sum_congr rfl this, sum_add_distrib, hcross]
    simp
    ring
  rw [← sum_add_sum_compl K, hKsum]
  ring

end BrouwerLaplacian.Dev.Split32
end

section
namespace BrouwerLaplacian.Dev.L32

open Finset Matrix BrouwerLaplacian

theorem prefix_of_antitone {m : ℕ} (f : Fin m → ℝ) (hf : Antitone f) (r : ℝ) :
    (univ.filter fun j => r < f j)
      = univ.filter (fun j : Fin m => j.val < #(univ.filter fun j => r < f j)) := by
  set T := univ.filter fun j => r < f j with hT
  have hmem : ∀ j, j ∈ T ↔ r < f j := fun j => by simp [hT]
  ext j
  rw [hmem]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hj
    have : (Iic j) ⊆ T := by
      intro j' hj'
      rw [mem_Iic] at hj'
      rw [hmem]
      exact lt_of_lt_of_le ((hmem j).1 ((hmem j).2 hj)) (hf hj')
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hnot
    have : T ⊆ Iio j := by
      intro j' hj'
      rw [hmem] at hj'
      rw [mem_Iio]
      by_contra hge
      have hge' : j ≤ j' := not_lt.1 hge
      have := hf hge'
      exact hnot (lt_of_lt_of_le hj' this)
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega

theorem sum_ev_eq_deg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∑ j : Fin (Fintype.card (Fin n)), (G.isHermitian_lapMatrix ℝ).eigenvalues₀ j
      = ∑ v, (G.degree v : ℝ) := by
  set hA := G.isHermitian_lapMatrix ℝ with hAdef
  have h1 : ∑ i : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ i = (G.lapMatrix ℝ).trace := by
    have := hA.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at this
    rw [this]
    exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm.sum_comp
      hA.eigenvalues₀ |>.symm
  rw [h1]
  simp [Matrix.trace, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]

theorem P_bound {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (K : Finset (Fin n)) :
    ∑ j : Fin (Fintype.card (Fin n)),
        max ((H.isHermitian_lapMatrix ℝ).eigenvalues₀ j - (#K : ℝ)) 0
      ≤ ∑ v ∈ Kᶜ, (H.degree v : ℝ) := by
  set hL := H.isHermitian_lapMatrix ℝ with hLdef
  set r : ℝ := (#K : ℝ) with hr
  set ev := hL.eigenvalues₀ with hev
  set E : ℝ := ∑ v ∈ Kᶜ, (H.degree v : ℝ) with hE
  have hE0 : 0 ≤ E := sum_nonneg fun v _ => Nat.cast_nonneg _
  set T := univ.filter fun j => r < ev j with hT
  have hP : ∑ j, max (ev j - r) 0 = ∑ j ∈ T, (ev j - r) := by
    rw [hT, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : r < ev j
    · rw [if_pos h, max_eq_left (by linarith)]
    · rw [if_neg h, max_eq_right (by linarith [not_lt.1 h])]
  rw [hP]
  by_cases ht : #T = 0
  · rw [Finset.card_eq_zero] at ht
    rw [ht]; simpa using hE0
  have hpre := prefix_of_antitone ev hL.eigenvalues₀_antitone r
  rw [← hT] at hpre
  have h1 : ∑ j ∈ T, (ev j - r) = ∑ j : Fin (Fintype.card (Fin n)) with j.val < #T, ev j - #T * r := by
    have hcard : #(univ.filter fun j : Fin (Fintype.card (Fin n)) => j.val < #T) = #T := by
      rw [Fin.card_filter_val_lt]; exact min_eq_right (by simpa using card_le_univ T)
    rw [hpre, sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]
  have hg := BrouwerLaplacian.theorem_1_2_grone_merris_bai H #T (Nat.pos_of_ne_zero ht)
    (by simpa using card_le_univ T)
  rw [Split32.conj_sum] at hg
  have hmin := Split32.min_sum_le H K #T
  have hmin' : (((∑ v, min (H.degree v) #T : ℕ)) : ℝ) ≤ r * #T + E := by
    have := (Nat.cast_le (α := ℝ)).2 hmin
    simpa [hr, hE] using this
  rw [h1]
  linarith

theorem main {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (K : Finset (Fin n))
    (hH : IsSplitWith H K) :
    WainwrightHDS.NucNorm.nucNorm (H.lapMatrix ℝ - (#K : ℝ) • centering n)
      ≤ (#K : ℝ) * (#Kᶜ : ℝ) := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [WainwrightHDS.NucNorm.nucNorm]
    positivity
  have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
  set hL := H.isHermitian_lapMatrix ℝ with hLdef
  set r : ℝ := (#K : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hA := Spec32.nuc_lap_sub H hn r
  rw [abs_of_nonneg hr0] at hA
  have habs : ∀ x : ℝ, |x| = 2 * max x 0 - x := by
    intro x; rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have hsum : ∑ j : Fin (Fintype.card (Fin n)), |hL.eigenvalues₀ j - r|
      = 2 * ∑ j : Fin (Fintype.card (Fin n)), max (hL.eigenvalues₀ j - r) 0
        - (∑ j : Fin (Fintype.card (Fin n)), hL.eigenvalues₀ j - (n : ℝ) * r) := by
    simp only [habs, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
  have hev := sum_ev_eq_deg H
  have hdeg := Split32.deg_sum H K hH
  have hP := P_bound H K
  have hcompl : (#Kᶜ : ℝ) = n - r := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using card_le_univ K)]
  rw [hcompl]
  rw [hsum, hev, hdeg] at hA
  nlinarith [hA, hP]

end BrouwerLaplacian.Dev.L32

namespace BrouwerLaplacian
open Finset
theorem chk_lemma_3_2 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (K : Finset (Fin n))
    (hH : IsSplitWith H K) :
    WainwrightHDS.NucNorm.nucNorm (H.lapMatrix ℝ - (#K : ℝ) • centering n)
      ≤ (#K : ℝ) * (#Kᶜ : ℝ) := Dev.L32.main H K hH
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_3_2 := @BrouwerLaplacian.chk_lemma_3_2
