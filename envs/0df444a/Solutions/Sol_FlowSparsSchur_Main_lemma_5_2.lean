-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:25:52.546168+00:00
-- url     : https://prove2.me/submissions/d951cfd8-44b5-49ca-93d7-d2d9df04ca1d

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace Aux52

open FlowSparsSchur.Main
open Matrix

section Penrose

variable {V : Type} [Fintype V]

lemma star_eq_transpose (M : Matrix V V ℝ) : star M = Mᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma penrose_unique {A X Y : Matrix V V ℝ}
    (hX : IsPenroseInverse A X) (hY : IsPenroseInverse A Y) : X = Y := by
  rcases hX with ⟨hAXA, hXAX, hAX_sym, hXA_sym⟩
  rcases hY with ⟨hAYA, hYAY, hAY_sym, hYA_sym⟩
  have hXA_eq : X * A = Y * A := by
    have h1 : X * A = (X * A) * (Y * A) := by
      calc X * A = X * (A * Y * A) := by rw [hAYA]
      _ = (X * A) * (Y * A) := by simp only [Matrix.mul_assoc]
    have h2 : Y * A = (Y * A) * (X * A) := by
      calc Y * A = Y * (A * X * A) := by rw [hAXA]
      _ = (Y * A) * (X * A) := by simp only [Matrix.mul_assoc]
    calc
      X * A = (X * A)ᵀ := hXA_sym.symm
      _ = ((X * A) * (Y * A))ᵀ := by rw [← h1]
      _ = (Y * A)ᵀ * (X * A)ᵀ := Matrix.transpose_mul _ _
      _ = (Y * A) * (X * A) := by rw [hYA_sym, hXA_sym]
      _ = Y * A := h2.symm
  have hAX_eq : A * X = A * Y := by
    have h1 : A * X = (A * Y) * (A * X) := by
      calc A * X = (A * Y * A) * X := by rw [hAYA]
      _ = (A * Y) * (A * X) := by simp only [Matrix.mul_assoc]
    have h2 : A * Y = (A * X) * (A * Y) := by
      calc A * Y = (A * X * A) * Y := by rw [hAXA]
      _ = (A * X) * (A * Y) := by simp only [Matrix.mul_assoc]
    calc
      A * X = (A * X)ᵀ := hAX_sym.symm
      _ = ((A * Y) * (A * X))ᵀ := by rw [← h1]
      _ = (A * X)ᵀ * (A * Y)ᵀ := Matrix.transpose_mul _ _
      _ = (A * X) * (A * Y) := by rw [hAX_sym, hAY_sym]
      _ = A * Y := h2.symm
  calc
    X = X * A * X := hXAX.symm
    _ = Y * A * X := by rw [hXA_eq]
    _ = Y * (A * X) := by simp only [Matrix.mul_assoc]
    _ = Y * (A * Y) := by rw [hAX_eq]
    _ = Y * A * Y := by simp only [Matrix.mul_assoc]
    _ = Y := hYAY

noncomputable def symPinv [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    Matrix V V ℝ :=
  (hA.eigenvectorUnitary : Matrix V V ℝ) *
    diagonal (fun i => (hA.eigenvalues i)⁻¹) *
    (hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ

lemma symPinv_isPenrose [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    IsPenroseInverse A (symPinv hA) := by
  let U : Matrix V V ℝ := hA.eigenvectorUnitary
  have hU_mem : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hU_mem' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hUUt : U * Uᵀ = 1 := by rwa [star_eq_transpose] at hU_mem
  have hUtU : Uᵀ * U = 1 := by rwa [star_eq_transpose] at hU_mem'
  have hspec : A = U * diagonal hA.eigenvalues * Uᵀ := by
    have hs := hA.spectral_theorem
    change A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U at hs
    rw [star_eq_transpose] at hs
    exact hs
  let D : Matrix V V ℝ := diagonal hA.eigenvalues
  let Dp : Matrix V V ℝ := diagonal (fun i => (hA.eigenvalues i)⁻¹)
  have hDDpD : D * Dp * D = D := by
    ext i j
    simp only [D, Dp, diagonal_mul_diagonal, diagonal_apply]
    split_ifs with h
    · by_cases hz : hA.eigenvalues i = 0 <;> simp [hz]
    · rfl
  have hDpDDp : Dp * D * Dp = Dp := by
    ext i j
    simp only [D, Dp, diagonal_mul_diagonal, diagonal_apply]
    split_ifs with h
    · by_cases hz : hA.eigenvalues i = 0 <;> simp [hz]
    · rfl
  have hDDp_sym : (U * (D * Dp) * Uᵀ)ᵀ = U * (D * Dp) * Uᵀ := by
    simp [D, Dp, diagonal_mul_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hDpD_sym : (U * (Dp * D) * Uᵀ)ᵀ = U * (Dp * D) * Uᵀ := by
    simp [D, Dp, diagonal_mul_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hAX : A * symPinv hA = U * (D * Dp) * Uᵀ := by
    calc
      A * symPinv hA = (U * D * Uᵀ) * (U * Dp * Uᵀ) := by rw [← hspec]; rfl
      _ = U * D * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hXA : symPinv hA * A = U * (Dp * D) * Uᵀ := by
    calc
      symPinv hA * A = (U * Dp * Uᵀ) * (U * D * Uᵀ) := by rw [← hspec]; rfl
      _ = U * Dp * (Uᵀ * U) * D * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (Dp * D) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      A * symPinv hA * A = (U * (D * Dp) * Uᵀ) * A := by rw [hAX]
      _ = (U * (D * Dp) * Uᵀ) * (U * D * Uᵀ) := by rw [← hspec]
      _ = U * (D * Dp) * (Uᵀ * U) * D * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp * D) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * D * Uᵀ := by rw [hDDpD]
      _ = A := hspec.symm
  · calc
      symPinv hA * A * symPinv hA = (U * (Dp * D) * Uᵀ) * (U * Dp * Uᵀ) := by
        rw [hXA]; rfl
      _ = U * (Dp * D) * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (Dp * D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = symPinv hA := by rw [hDpDDp]; rfl
  · rw [hAX, hDDp_sym]
  · rw [hXA, hDpD_sym]

lemma pinv_eq_symPinv [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    pinv A = symPinv hA := by
  unfold pinv
  have hex : ∃ X, IsPenroseInverse A X := ⟨symPinv hA, symPinv_isPenrose hA⟩
  rw [dif_pos hex]
  exact penrose_unique hex.choose_spec (symPinv_isPenrose hA)

lemma mul_pinv_mulVec_of_ortho_ker [DecidableEq V] {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (d : V → ℝ) (hd : ∀ z : V → ℝ, A *ᵥ z = 0 → z ⬝ᵥ d = 0) :
    (A * pinv A) *ᵥ d = d := by
  rw [pinv_eq_symPinv hA]
  let U : Matrix V V ℝ := hA.eigenvectorUnitary
  have hU_mem : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hU_mem' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hUUt : U * Uᵀ = 1 := by rwa [star_eq_transpose] at hU_mem
  have hUtU : Uᵀ * U = 1 := by rwa [star_eq_transpose] at hU_mem'
  have hspec : A = U * diagonal hA.eigenvalues * Uᵀ := by
    have hs := hA.spectral_theorem
    change A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U at hs
    rw [star_eq_transpose] at hs
    exact hs
  let D : Matrix V V ℝ := diagonal hA.eigenvalues
  let Dp : Matrix V V ℝ := diagonal (fun i => (hA.eigenvalues i)⁻¹)
  have hAX : A * symPinv hA = U * (D * Dp) * Uᵀ := by
    calc
      A * symPinv hA = (U * D * Uᵀ) * (U * Dp * Uᵀ) := by rw [← hspec]; rfl
      _ = U * D * (Uᵀ * U) * Dp * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * Dp) * Uᵀ := by rw [hUtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hAX]
  have hcol : ∀ i : V, hA.eigenvalues i = 0 → (Uᵀ *ᵥ d) i = 0 := by
    intro i hi0
    let z : V → ℝ := fun v => U v i
    have hUtz : Uᵀ *ᵥ z = Pi.single i 1 := by
      ext j
      have hentry := congr_fun (congr_fun hUtU j) i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hentry
      simpa [z, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, eq_comm]
        using hentry
    have hAz : A *ᵥ z = 0 := by
      calc
        A *ᵥ z = (U * D * Uᵀ) *ᵥ z := by rw [← hspec]
        _ = U *ᵥ (D *ᵥ (Uᵀ *ᵥ z)) := by simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        _ = U *ᵥ (D *ᵥ Pi.single i 1) := by rw [hUtz]
        _ = 0 := by
            ext v
            simp [D, Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply, hi0]
    have hzd := hd z hAz
    simpa [z, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hzd
  have hDDp_vec : (D * Dp) *ᵥ (Uᵀ *ᵥ d) = Uᵀ *ᵥ d := by
    ext i
    simp only [D, Dp, diagonal_mul_diagonal, mulVec_diagonal]
    by_cases hi0 : hA.eigenvalues i = 0
    · rw [hcol i hi0, mul_zero]
    · rw [mul_inv_cancel₀ hi0, one_mul]
  calc
    (U * (D * Dp) * Uᵀ) *ᵥ d = U *ᵥ ((D * Dp) *ᵥ (Uᵀ *ᵥ d)) := by
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = U *ᵥ (Uᵀ *ᵥ d) := by rw [hDDp_vec]
    _ = (U * Uᵀ) *ᵥ d := by rw [Matrix.mulVec_mulVec]
    _ = d := by rw [hUUt, Matrix.one_mulVec]

end Penrose

section GraphLap

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma lap_isHermitian (G : CGraph V E) : G.lap.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [CGraph.lap, CGraph.condMat, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma incidence_mulVec (G : CGraph V E) (x : V → ℝ) (e : E) :
    (G.incidence *ᵥ x) e = x (G.src e) - x (G.dst e) := by
  simp [CGraph.incidence, Matrix.mulVec, dotProduct, sub_mul]

lemma dotProduct_lap_mulVec (G : CGraph V E) (x y : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ y) =
      ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) * (y (G.src e) - y (G.dst e)) := by
  have h1 : x ⬝ᵥ (G.lap *ᵥ y) = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
    calc
      x ⬝ᵥ (G.lap *ᵥ y)
          = x ⬝ᵥ (G.incidenceᵀ *ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y))) := by
              simp only [CGraph.lap, Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (x ᵥ* G.incidenceᵀ) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) :=
            Matrix.dotProduct_mulVec x G.incidenceᵀ _
      _ = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
            rw [Matrix.vecMul_transpose]
  rw [h1]
  simp only [dotProduct, CGraph.condMat, mulVec_diagonal, incidence_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma quad_lap_eq (G : CGraph V E) (x : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ x) = ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) ^ 2 := by
  rw [dotProduct_lap_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma lap_ker_const (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    {z : V → ℝ} (hz : G.lap *ᵥ z = 0) (u v : V) : z u = z v := by
  have hquad : ∑ e : E, G.cond e * (z (G.src e) - z (G.dst e)) ^ 2 = 0 := by
    rw [← quad_lap_eq, hz, dotProduct_zero]
  have hedge_zero : ∀ e : E, z (G.src e) = z (G.dst e) := by
    intro e
    have hnn : ∀ e' ∈ (Finset.univ : Finset E),
        0 ≤ G.cond e' * (z (G.src e') - z (G.dst e')) ^ 2 :=
      fun e' _ => mul_nonneg (le_of_lt (hpos e')) (sq_nonneg _)
    have he0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hquad e (Finset.mem_univ e)
    have hsq : (z (G.src e) - z (G.dst e)) ^ 2 = 0 :=
      (mul_eq_zero.mp he0).resolve_left (ne_of_gt (hpos e))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hadj : ∀ a b : V, G.Adj a b → z a = z b := by
    intro a b hab
    rcases hab with ⟨e, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩⟩
    · exact hedge_zero e
    · exact (hedge_zero e).symm
  exact Relation.ReflTransGen.head_induction_on (hconn u v) rfl
    (fun {a b} hab _ ih => (hadj a b hab).trans ih)

lemma lap_mul_pinv_mulVec_of_sum_zero [Nonempty V] (G : CGraph V E)
    (hpos : G.PosCond) (hconn : G.Connected) {d : V → ℝ} (hd : ∑ v : V, d v = 0) :
    (G.lap * pinv G.lap) *ᵥ d = d := by
  refine mul_pinv_mulVec_of_ortho_ker (lap_isHermitian G) d ?_
  intro z hz
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hconst : ∀ v : V, z v = z v₀ := fun v => lap_ker_const G hpos hconn hz v v₀
  calc
    z ⬝ᵥ d = ∑ v : V, z v * d v := rfl
    _ = ∑ v : V, z v₀ * d v := Finset.sum_congr rfl fun v _ => by rw [hconst v]
    _ = z v₀ * ∑ v : V, d v := by rw [← Finset.mul_sum]
    _ = 0 := by rw [hd, mul_zero]

lemma lap_mul_pinv_mul_of_col_sum_zero [Nonempty V] {J : Type} [Fintype J]
    (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (D : Matrix V J ℝ) (hD : ∀ j : J, ∑ v : V, D v j = 0) :
    (G.lap * pinv G.lap) * D = D := by
  ext v j
  have hcol := congr_fun (lap_mul_pinv_mulVec_of_sum_zero G hpos hconn (hD j)) v
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hcol

lemma schurProj_mul_padOf {L : Matrix V V ℝ} (S : Finset V) :
    schurProjOf L S * padOf S = 1 := by
  ext s₁ s₂
  rw [Matrix.mul_apply]
  have hsum : (∑ v : V, schurProjOf L S s₁ v * padOf S v s₂) =
      schurProjOf L S s₁ s₂.val := by
    simp [padOf]
  rw [hsum]
  by_cases h : s₁ = s₂
  · subst h; simp [schurProjOf, s₁.prop]
  · have hv : s₁.val ≠ s₂.val := fun hv => h (Subtype.ext hv)
    simp [schurProjOf, s₂.prop, h, hv]

end GraphLap

end Aux52

open FlowSparsSchur.Main
open Matrix

theorem solution {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (H : CGraph S (Fin r)) (hS : 2 ≤ S.card) (hG : G.IsCapCondGraph) (hH : H.IsCondGraph) :
    QEmbeds 1 G (H.withCap (domCap S G H)) (fun s : S => s.val) (fun s : S => s) := by
  have hS_ne : Nonempty S := by
    rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  intro a D hD hRout
  rcases hRout with ⟨F, hRoutes, hLoad⟩
  let Fpart : Matrix (Fin m) (Fin a) ℝ := Matrix.of fun e j => (G.cap e)⁻¹ * F e j
  let FH : Matrix (Fin r) (Fin a) ℝ := fwdEmb S G H * Fpart
  refine ⟨FH, ?_, ?_⟩
  · unfold Routes
    have hcap_cancel : G.capMat * Fpart = F := by
      ext e j
      have hne : G.cap e ≠ 0 := ne_of_gt (hG.2 e)
      rw [CGraph.capMat, Matrix.diagonal_mul]
      simp [Fpart, mul_inv_cancel_left₀ hne]
    have hpadD : extendDemand (fun s : S => s.val) D = padOf S * D := by
      ext v j
      simp only [extendDemand, Matrix.mul_apply, padOf]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hvs : v = s.val
      · subst hvs; simp
      · have hsv : s.val ≠ v := Ne.symm hvs
        simp [hvs, hsv]
    have hidD : extendDemand (fun s : S => s) D = D := by
      ext s j
      simp [extendDemand]
    have hinc_withCap : (H.withCap (domCap S G H)).incidence = H.incidence := rfl
    rw [hinc_withCap, hidD]
    calc
      H.incidenceᵀ * FH
          = H.incidenceᵀ * (H.condMat * H.incidence * pinv H.lap * schurProj G S *
              G.incidenceᵀ * G.capMat * Fpart) := rfl
      _ = H.incidenceᵀ * H.condMat * H.incidence * pinv H.lap * schurProj G S *
            (G.incidenceᵀ * (G.capMat * Fpart)) := by
            simp only [Matrix.mul_assoc]
      _ = (H.lap * pinv H.lap) * (schurProj G S * (G.incidenceᵀ * F)) := by
            rw [hcap_cancel]
            simp only [CGraph.lap, Matrix.mul_assoc]
      _ = (H.lap * pinv H.lap) * ((schurProj G S * padOf S) * D) := by
            rw [hRoutes, hpadD]
            simp only [Matrix.mul_assoc]
      _ = (H.lap * pinv H.lap) * D := by
            rw [schurProj, Aux52.schurProj_mul_padOf, Matrix.one_mul]
      _ = D := Aux52.lap_mul_pinv_mul_of_col_sum_zero H hH.2.1 hH.2.2 D hD
  · intro f
    have hentry : ∀ j : Fin a, |FH f j| ≤
        ∑ e : Fin m, |fwdEmb S G H f e| * (G.cap e)⁻¹ * |F e j| := by
      intro j
      have hFH : FH f j = ∑ e : Fin m, fwdEmb S G H f e * ((G.cap e)⁻¹ * F e j) := by
        dsimp only [FH]
        rw [Matrix.mul_apply]
        rfl
      rw [hFH]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun e _ => ?_
      have hpos : 0 ≤ (G.cap e)⁻¹ := inv_nonneg.mpr (le_of_lt (hG.2 e))
      rw [abs_mul, abs_mul, abs_of_nonneg hpos, mul_assoc]
    calc
      load FH f = ∑ j : Fin a, |FH f j| := rfl
      _ ≤ ∑ j : Fin a, ∑ e : Fin m, |fwdEmb S G H f e| * (G.cap e)⁻¹ * |F e j| :=
          Finset.sum_le_sum fun j _ => hentry j
      _ = ∑ e : Fin m, |fwdEmb S G H f e| * (G.cap e)⁻¹ * load F e := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.mul_sum]
          rfl
      _ ≤ ∑ e : Fin m, |fwdEmb S G H f e| * (G.cap e)⁻¹ * (1 * G.cap e) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have hnn : 0 ≤ |fwdEmb S G H f e| * (G.cap e)⁻¹ :=
            mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (le_of_lt (hG.2 e)))
          exact mul_le_mul_of_nonneg_left (hLoad e) hnn
      _ = 1 * (H.withCap (domCap S G H)).cap f := by
          simp only [CGraph.withCap, domCap, one_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          have hne : G.cap e ≠ 0 := ne_of_gt (hG.2 e)
          field_simp [hne]
