-- Prove2me | solution 1 for BaconThesis.Universality.lemma_4_3_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:52:46.580409+00:00
-- url     : https://prove2.me/submissions/a136a464-c767-4c81-a8c8-995069606fb7

import Mathlib
import Definitions.Def_BaconThesis_Universality_denseGen
import Definitions.Def_BaconThesis_Universality_SUOn

open Matrix WithLp

namespace BaconThesis.Universality.Sol431

open BaconThesis.Universality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Matrices acting on `EuclideanSpace` -/

noncomputable def act (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin U v

lemma act_def (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : act U v = toLp 2 (U *ᵥ ofLp v) := rfl

lemma mem_SUOn {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} :
    U ∈ SUOn W ↔ U ∈ Matrix.specialUnitaryGroup ι ℂ ∧ ∀ v ∈ Wᗮ, act U v = v := Iff.rfl

lemma act_mul (U V : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : act (U * V) v = act U (act V v) := by
  simp [act_def, mulVec_mulVec]

lemma act_one (v : EuclideanSpace ℂ ι) : act 1 v = v := by simp [act_def]

lemma act_add (U : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) : act U (v + w) = act U v + act U w :=
  LinearMap.map_add _ _ _

lemma act_smul (U : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) : act U (c • v) = c • act U v :=
  LinearMap.map_smul _ _ _

lemma inner_act (U : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act U x) y = inner ℂ x (act Uᴴ y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act_def, WithLp.ofLp_toLp]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

lemma unitary_star_mul {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) : Uᴴ * U = 1 :=
  mem_unitaryGroup_iff'.1 hU

lemma unitary_mul_star {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) : U * Uᴴ = 1 :=
  mem_unitaryGroup_iff.1 hU

lemma inner_act_act {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ι) : inner ℂ (act U x) (act U y) = inner ℂ x y := by
  rw [inner_act, ← act_mul, unitary_star_mul hU, act_one]

lemma norm_act {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (x : EuclideanSpace ℂ ι) :
    ‖act U x‖ = ‖x‖ := by
  have h := inner_act_act hU x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have : ‖act U x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-! ### `SUOn` basics -/

lemma SUOn_SU {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} (h : U ∈ SUOn W) :
    U ∈ Matrix.specialUnitaryGroup ι ℂ := h.1

lemma SUOn_U {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} (h : U ∈ SUOn W) :
    U ∈ Matrix.unitaryGroup ι ℂ := (mem_specialUnitaryGroup_iff.1 h.1).1

lemma SUOn_fix {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} (h : U ∈ SUOn W)
    {v : EuclideanSpace ℂ ι} (hv : v ∈ Wᗮ) : act U v = v := (mem_SUOn.1 h).2 v hv

lemma SUOn_one (W : Submodule ℂ (EuclideanSpace ℂ ι)) : (1 : Matrix ι ι ℂ) ∈ SUOn W :=
  mem_SUOn.2 ⟨one_mem _, fun v _ => act_one v⟩

lemma SUOn_mul {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U V : Matrix ι ι ℂ} (hU : U ∈ SUOn W)
    (hV : V ∈ SUOn W) : U * V ∈ SUOn W :=
  mem_SUOn.2 ⟨mul_mem hU.1 hV.1, fun v hv => by rw [act_mul, SUOn_fix hV hv, SUOn_fix hU hv]⟩

lemma SUOn_star {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} (hU : U ∈ SUOn W) :
    Uᴴ ∈ SUOn W := by
  refine mem_SUOn.2 ⟨?_, fun v hv => ?_⟩
  · obtain ⟨hu, hd⟩ := mem_specialUnitaryGroup_iff.1 hU.1
    refine mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩
    · rw [mem_unitaryGroup_iff, ← star_eq_conjTranspose, star_star]
      exact mem_unitaryGroup_iff'.1 hu
    · rw [det_conjTranspose, hd, star_one]
  · conv_lhs => rw [← SUOn_fix hU hv]
    rw [← act_mul, unitary_star_mul (SUOn_U hU), act_one]

lemma SUOn_mono {W W' : Submodule ℂ (EuclideanSpace ℂ ι)} (h : W ≤ W') : SUOn W ⊆ SUOn W' :=
  fun _ hU => mem_SUOn.2 ⟨hU.1, fun v hv => SUOn_fix hU (Submodule.orthogonal_le h hv)⟩

lemma SUOn_maps {W : Submodule ℂ (EuclideanSpace ℂ ι)} {U : Matrix ι ι ℂ} (hU : U ∈ SUOn W)
    {v : EuclideanSpace ℂ ι} (hv : v ∈ W) : act U v ∈ W := by
  rw [← Submodule.orthogonal_orthogonal W, Submodule.mem_orthogonal]
  intro w hw
  have := inner_act_act (SUOn_U hU) w v
  rw [SUOn_fix hU hw] at this
  rw [this]
  exact Submodule.inner_left_of_mem_orthogonal hv hw


/-! ### Special unitaries on a plane -/

/-- The `ι × 2` matrix with columns `f₁, f₂`. -/
noncomputable def Fm (f1 f2 : EuclideanSpace ℂ ι) : Matrix ι (Fin 2) ℂ :=
  Matrix.of fun k i => ofLp (![f1, f2] i) k

/-- `M` acting on `span {f₁, f₂}` (in the basis `f₁, f₂`), the identity on its complement. -/
noncomputable def plane (f1 f2 : EuclideanSpace ℂ ι) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ι ι ℂ :=
  1 + Fm f1 f2 * (M - 1) * (Fm f1 f2)ᴴ

structure ON (f1 f2 : EuclideanSpace ℂ ι) : Prop where
  n1 : inner ℂ f1 f1 = 1
  n2 : inner ℂ f2 f2 = 1
  o12 : inner ℂ f1 f2 = 0

lemma ON.o21 {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) : inner ℂ f2 f1 = 0 := by
  rw [← inner_conj_symm, h.o12, map_zero]

lemma ON.norm1 {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) : ‖f1‖ = 1 := by
  have h3 : ‖f1‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, h.n1]; simp
  nlinarith [norm_nonneg f1]

lemma ON.norm2 {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) : ‖f2‖ = 1 := by
  have h3 : ‖f2‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, h.n2]; simp
  nlinarith [norm_nonneg f2]

lemma Fm_star_mulVec (f1 f2 v : EuclideanSpace ℂ ι) :
    (Fm f1 f2)ᴴ *ᵥ ofLp v = ![inner ℂ f1 v, inner ℂ f2 v] := by
  ext i
  fin_cases i <;>
    simp [Fm, mulVec, dotProduct, EuclideanSpace.inner_eq_star_dotProduct, conjTranspose_apply,
      mul_comm]

lemma Fm_mulVec (f1 f2 : EuclideanSpace ℂ ι) (w : Fin 2 → ℂ) :
    toLp 2 (Fm f1 f2 *ᵥ w) = w 0 • f1 + w 1 • f2 := by
  ext k
  simp [Fm, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

lemma Fm_star_Fm {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) : (Fm f1 f2)ᴴ * Fm f1 f2 = 1 := by
  ext i j
  have e : ∀ i j, ((Fm f1 f2)ᴴ * Fm f1 f2) i j = inner ℂ (![f1, f2] i) (![f1, f2] j) := by
    intro i j
    simp [Fm, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      conjTranspose_apply, mul_comm]
  rw [e]
  fin_cases i <;> fin_cases j <;> simp [h.norm1, h.norm2, h.o12, h.o21]

lemma act_plane (f1 f2 : EuclideanSpace ℂ ι) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ ι) :
    act (plane f1 f2 M) v = v + (((M - 1) *ᵥ ![inner ℂ f1 v, inner ℂ f2 v]) 0 • f1 +
      ((M - 1) *ᵥ ![inner ℂ f1 v, inner ℂ f2 v]) 1 • f2) := by
  rw [act_def, plane, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    Fm_star_mulVec, WithLp.toLp_add, Fm_mulVec]

lemma plane_fix (f1 f2 : EuclideanSpace ℂ ι) (M : Matrix (Fin 2) (Fin 2) ℂ)
    {v : EuclideanSpace ℂ ι} (h1 : inner ℂ f1 v = 0) (h2 : inner ℂ f2 v = 0) :
    act (plane f1 f2 M) v = v := by
  rw [act_plane, h1, h2]
  simp

lemma plane_f1 {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    act (plane f1 f2 M) f1 = M 0 0 • f1 + M 1 0 • f2 := by
  rw [act_plane, h.n1, h.o21]
  simp [mulVec, dotProduct, Fin.sum_univ_two, sub_smul]
  abel

lemma plane_SU {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    plane f1 f2 M ∈ Matrix.specialUnitaryGroup ι ℂ := by
  obtain ⟨hu, hd⟩ := mem_specialUnitaryGroup_iff.1 hM
  have hFF := Fm_star_Fm h
  have hMM : Mᴴ * M = 1 := mem_unitaryGroup_iff'.1 hu
  refine mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, plane]
    set F := Fm f1 f2
    have hY : (M - 1)ᴴ = Mᴴ - 1 := by rw [conjTranspose_sub, conjTranspose_one]
    have hc : (1 + F * (M - 1) * Fᴴ)ᴴ = 1 + F * (M - 1)ᴴ * Fᴴ := by
      rw [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hc, hY]
    generalize hG : Fᴴ = G at hFF ⊢
    have e : ∀ X Y : Matrix (Fin 2) (Fin 2) ℂ, (1 + F * Y * G) * (1 + F * X * G) =
        1 + F * (Y + X + Y * (G * F) * X) * G := fun X Y => by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [e, hFF, Matrix.mul_one]
    have : Mᴴ - 1 + (M - 1) + (Mᴴ - 1) * (M - 1) = Mᴴ * M - 1 := by noncomm_ring
    rw [this, hMM, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [plane, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc, hFF, Matrix.mul_one,
      add_sub_cancel, hd]

lemma plane_SUOn {W : Submodule ℂ (EuclideanSpace ℂ ι)} {f1 f2 : EuclideanSpace ℂ ι}
    (h : ON f1 f2) (h1 : f1 ∈ W) (h2 : f2 ∈ W) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : plane f1 f2 M ∈ SUOn W :=
  mem_SUOn.2 ⟨plane_SU h hM, fun _ hv => plane_fix f1 f2 M
    (Submodule.inner_right_of_mem_orthogonal h1 hv) (Submodule.inner_right_of_mem_orthogonal h2 hv)⟩


/-! ### Transitivity of `SU(W)` on spheres of `W` -/

open ComplexConjugate in
def rot (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![p, -conj q; q, conj p]

open ComplexConjugate in
lemma rot_SU {p q : ℂ} (h : conj p * p + conj q * q = 1) :
    rot p q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine mem_specialUnitaryGroup_iff.2 ⟨mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def] <;>
      first | ring1 | linear_combination h
  · simp [rot, det_fin_two]; linear_combination h

lemma inner_normalize {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    inner ℂ (((‖v‖ : ℂ)⁻¹) • v) (((‖v‖ : ℂ)⁻¹) • v) = 1 := by
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [map_inv₀, Complex.conj_ofReal]
  field_simp
  rfl

lemma exists_perp {W : Submodule ℂ (EuclideanSpace ℂ ι)} (hW : 2 ≤ Module.finrank ℂ W)
    {f1 : EuclideanSpace ℂ ι} (hf1W : f1 ∈ W) :
    ∃ f2 ∈ W, inner ℂ f2 f2 = 1 ∧ inner ℂ f1 f2 = 0 := by
  have hle : (ℂ ∙ f1) ⊓ W ≤ W := inf_le_right
  have h1 := Submodule.finrank_add_inf_finrank_orthogonal hle
  have h2 : Module.finrank ℂ ((ℂ ∙ f1) ⊓ W : Submodule ℂ _) ≤ 1 := by
    refine (Submodule.finrank_mono inf_le_left).trans ?_
    have := finrank_span_le_card (R := ℂ) ({f1} : Set (EuclideanSpace ℂ ι))
    simpa using this
  have hne : (((ℂ ∙ f1) ⊓ W)ᗮ ⊓ W : Submodule ℂ (EuclideanSpace ℂ ι)) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, W.smul_mem _ (Submodule.mem_inf.1 hv).2, inner_normalize hv0, ?_⟩
  rw [inner_smul_right,
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨Submodule.mem_span_singleton_self f1, hf1W⟩) (Submodule.mem_inf.1 hv).1,
    mul_zero]

open ComplexConjugate in
lemma trans_on {W : Submodule ℂ (EuclideanSpace ℂ ι)} (hW : 2 ≤ Module.finrank ℂ W)
    {x x' : EuclideanSpace ℂ ι} (hx : x ∈ W) (hx' : x' ∈ W) (hn : ‖x‖ = ‖x'‖) :
    ∃ U ∈ SUOn W, act U x = x' := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [norm_zero, eq_comm, norm_eq_zero] at hn
    exact ⟨1, SUOn_one W, by rw [hn, act_one]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ = (‖x‖ : ℂ) := ⟨_, rfl⟩
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact_mod_cast norm_ne_zero_iff.2 hx0
  obtain ⟨f1, hf1⟩ : ∃ f1, f1 = ρ⁻¹ • x := ⟨_, rfl⟩
  have hf1W : f1 ∈ W := by rw [hf1]; exact W.smul_mem _ hx
  have h11 : inner ℂ f1 f1 = 1 := by rw [hf1, hρ]; exact inner_normalize hx0
  have hxf : x = ρ • f1 := by rw [hf1, smul_smul, mul_inv_cancel₀ hρ0, one_smul]
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = inner ℂ f1 x' := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x' - a1 • f1 := ⟨_, rfl⟩
  have hyW : y ∈ W := by rw [hy]; exact W.sub_mem hx' (W.smul_mem _ hf1W)
  have h1y : inner ℂ f1 y = 0 := by
    rw [hy, inner_sub_right, inner_smul_right, h11, mul_one, ha1, sub_self]
  obtain ⟨f2, hf2W, h22, h12, hdec⟩ : ∃ f2 ∈ W, inner ℂ f2 f2 = 1 ∧ inner ℂ f1 f2 = 0 ∧
      x' = a1 • f1 + inner ℂ f2 x' • f2 := by
    by_cases hy0 : y = 0
    · obtain ⟨f2, hf2W, h22, h12⟩ := exists_perp hW hf1W
      refine ⟨f2, hf2W, h22, h12, ?_⟩
      have hx'e : x' = a1 • f1 := by rw [← sub_eq_zero, ← hy]; exact hy0
      have : inner ℂ f2 x' = 0 := by
        rw [hx'e, inner_smul_right, ← inner_conj_symm, h12, map_zero, mul_zero]
      rw [this, zero_smul, add_zero]; exact hx'e
    · refine ⟨((‖y‖ : ℂ)⁻¹) • y, W.smul_mem _ hyW, inner_normalize hy0, ?_, ?_⟩
      · rw [inner_smul_right, h1y, mul_zero]
      · have hyn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy0
        have hyx : inner ℂ y x' = (‖y‖ : ℂ) ^ 2 := by
          have : x' = y + a1 • f1 := by rw [hy, sub_add_cancel]
          have hy1 : inner ℂ y f1 = 0 := by rw [← inner_conj_symm, h1y, map_zero]
          rw [this, inner_add_right, inner_smul_right, hy1, mul_zero, add_zero,
            inner_self_eq_norm_sq_to_K]
          rfl
        rw [inner_smul_left, hyx, smul_smul]
        simp only [map_inv₀, Complex.conj_ofReal]
        rw [show (‖y‖ : ℂ)⁻¹ * (‖y‖ : ℂ) ^ 2 * (‖y‖ : ℂ)⁻¹ = 1 by field_simp, one_smul, hy,
          add_sub_cancel]
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = inner ℂ f2 x' := ⟨_, rfl⟩
  rw [← ha2] at hdec
  have hON : ON f1 f2 := ⟨h11, h22, h12⟩
  have hsum : conj a1 * a1 + conj a2 * a2 = ρ * ρ := by
    have e1 : inner ℂ x' x' = conj a1 * a1 + conj a2 * a2 := by
      conv_lhs => rw [hdec]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h11, h22,
        h12, hON.o21]
      ring
    have e2 : inner ℂ x' x' = ρ * ρ := by
      rw [inner_self_eq_norm_sq_to_K, hρ, ← hn, sq]; rfl
    rw [← e1, e2]
  refine ⟨plane f1 f2 (rot (a1 / ρ) (a2 / ρ)), plane_SUOn hON hf1W hf2W (rot_SU ?_), ?_⟩
  · have hc : conj ρ = ρ := by rw [hρ, Complex.conj_ofReal]
    rw [map_div₀, map_div₀, hc]
    field_simp
    linear_combination hsum
  · rw [hxf, act_smul, plane_f1 hON]
    simp only [rot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hρ0, mul_div_cancel₀ _ hρ0]
    exact hdec.symm


/-! ### Orthonormal pairs -/

lemma ON.finrank {W : Submodule ℂ (EuclideanSpace ℂ ι)} {f1 f2 : EuclideanSpace ℂ ι}
    (h : ON f1 f2) (h1 : f1 ∈ W) (h2 : f2 ∈ W) : 2 ≤ Module.finrank ℂ W := by
  have hon : Orthonormal ℂ ![f1, f2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h.norm1, h.norm2, h.o12, h.o21]
  have hli := hon.linearIndependent
  have hcard := finrank_span_eq_card hli
  have hle : Submodule.span ℂ (Set.range ![f1, f2]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simpa
  have := Submodule.finrank_mono hle
  simp only [Fintype.card_fin] at hcard
  omega

lemma ON.norm_sq {f1 f2 : EuclideanSpace ℂ ι} (h : ON f1 f2) (s t : ℂ) :
    ‖s • f1 + t • f2‖ ^ 2 = ‖s‖ ^ 2 + ‖t‖ ^ 2 := by
  have h0 : inner ℂ (s • f1) (t • f2) = 0 := by
    rw [inner_smul_left, inner_smul_right, h.o12]; simp
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sq, sq, sq, this, norm_smul, norm_smul, h.norm1, h.norm2]
  ring

lemma mem_orth_pair {f1 f2 v : EuclideanSpace ℂ ι} (h1 : inner ℂ f1 v = 0)
    (h2 : inner ℂ f2 v = 0) : v ∈ (Submodule.span ℂ {f1, f2})ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hu
  rw [inner_add_left, inner_smul_left, inner_smul_left, h1, h2]; simp

lemma mem_pair (f1 f2 : EuclideanSpace ℂ ι) (s t : ℂ) :
    s • f1 + t • f2 ∈ Submodule.span ℂ {f1, f2} :=
  Submodule.mem_span_pair.2 ⟨s, t, rfl⟩

/-! ### Stabiliser of a unit vector -/

lemma stab {A : Submodule ℂ (EuclideanSpace ℂ ι)} {c : EuclideanSpace ℂ ι}
    (hcc : inner ℂ c c = 1) (hc : c ∈ Aᗮ) {V : Matrix ι ι ℂ} (hV : V ∈ SUOn (A ⊔ ℂ ∙ c))
    (hVc : act V c = c) : V ∈ SUOn A := by
  refine mem_SUOn.2 ⟨hV.1, fun v hv => ?_⟩
  have hw : v - inner ℂ c v • c ∈ (A ⊔ ℂ ∙ c)ᗮ := by
    rw [← Submodule.inf_orthogonal]
    refine ⟨Aᗮ.sub_mem hv (Aᗮ.smul_mem _ hc), ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      inner_smul_right, hcc, mul_one, sub_self]
  have e : v = (v - inner ℂ c v • c) + inner ℂ c v • c := by abel
  rw [e, act_add, act_smul, SUOn_fix hV hw, hVc]

/-! ### Groups of matrices and reachability -/

structure Grp (M : Set (Matrix ι ι ℂ)) : Prop where
  one : (1 : Matrix ι ι ℂ) ∈ M
  mul : ∀ {U V}, U ∈ M → V ∈ M → U * V ∈ M
  star : ∀ {U}, U ∈ M → Uᴴ ∈ M

/-- `u` is carried to `v` by an element of `M ∩ SUOn W`. -/
def Rch (M : Set (Matrix ι ι ℂ)) (W : Submodule ℂ (EuclideanSpace ℂ ι))
    (u v : EuclideanSpace ℂ ι) : Prop :=
  ∃ g, g ∈ M ∧ g ∈ SUOn W ∧ act g u = v

variable {M : Set (Matrix ι ι ℂ)} {W : Submodule ℂ (EuclideanSpace ℂ ι)}

lemma Rch.refl (hM : Grp M) (u : EuclideanSpace ℂ ι) : Rch M W u u :=
  ⟨1, hM.one, SUOn_one W, act_one u⟩

lemma Rch.trans (hM : Grp M) {u v w : EuclideanSpace ℂ ι} (h1 : Rch M W u v)
    (h2 : Rch M W v w) : Rch M W u w := by
  obtain ⟨g, hg, hgS, rfl⟩ := h1
  obtain ⟨g', hg', hg'S, rfl⟩ := h2
  exact ⟨g' * g, hM.mul hg' hg, SUOn_mul hg'S hgS, act_mul _ _ _⟩

lemma Rch.symm (hM : Grp M) {u v : EuclideanSpace ℂ ι} (h : Rch M W u v) : Rch M W v u := by
  obtain ⟨g, hg, hgS, rfl⟩ := h
  exact ⟨gᴴ, hM.star hg, SUOn_star hgS, by rw [← act_mul, unitary_star_mul (SUOn_U hgS), act_one]⟩

lemma Rch.norm {u v : EuclideanSpace ℂ ι} (h : Rch M W u v) : ‖u‖ = ‖v‖ := by
  obtain ⟨g, -, hgS, rfl⟩ := h
  exact (norm_act (SUOn_U hgS) u).symm

/-- A step using `SU(V)` for a subspace `V ≤ W` contained in `M`. -/
lemma Rch.step {V : Submodule ℂ (EuclideanSpace ℂ ι)} (hVW : V ≤ W) (hVM : SUOn V ⊆ M)
    (hV2 : 2 ≤ Module.finrank ℂ V) {x x' w : EuclideanSpace ℂ ι} (hx : x ∈ V) (hx' : x' ∈ V)
    (hn : ‖x‖ = ‖x'‖) (hw : w ∈ Vᗮ) : Rch M W (x + w) (x' + w) := by
  obtain ⟨U, hU, hUx⟩ := trans_on hV2 hx hx' hn
  exact ⟨U, hVM hU, SUOn_mono hVW hU, by rw [act_add, hUx, SUOn_fix hU hw]⟩


/-! ### Adding one direction: the three-dimensional core -/

structure CSetup (A : Submodule ℂ (EuclideanSpace ℂ ι)) (e a c : EuclideanSpace ℂ ι) (α β : ℝ) :
    Prop where
  he : e ∈ A
  ha : a ∈ A
  hc : c ∈ Aᗮ
  hea : ON e a
  hcc : inner ℂ c c = 1
  hα : 0 ≤ α
  hβ : 0 < β
  hαβ : α ^ 2 + β ^ 2 = 1

/-- `b = α a + β c`. -/
noncomputable def bv (a c : EuclideanSpace ℂ ι) (α β : ℝ) : EuclideanSpace ℂ ι :=
  (α : ℂ) • a + (β : ℂ) • c

/-- `n = -β a + α c`, orthogonal to `e` and `b`. -/
noncomputable def nv (a c : EuclideanSpace ℂ ι) (α β : ℝ) : EuclideanSpace ℂ ι :=
  (-(β : ℂ)) • a + (α : ℂ) • c

namespace CSetup

variable {A : Submodule ℂ (EuclideanSpace ℂ ι)} {e a c : EuclideanSpace ℂ ι} {α β : ℝ}
  (S : CSetup A e a c α β)
include S

lemma ec : inner ℂ e c = 0 := Submodule.inner_right_of_mem_orthogonal S.he S.hc
lemma ac : inner ℂ a c = 0 := Submodule.inner_right_of_mem_orthogonal S.ha S.hc
lemma ce : inner ℂ c e = 0 := by rw [← inner_conj_symm, S.ec, map_zero]
lemma ca : inner ℂ c a = 0 := by rw [← inner_conj_symm, S.ac, map_zero]

lemma hαβc : (α : ℂ) ^ 2 + (β : ℂ) ^ 2 = 1 := by exact_mod_cast S.hαβ

lemma eb : ON e (bv a c α β) := by
  refine ⟨S.hea.n1, ?_, ?_⟩
  · simp only [bv, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      S.hea.n2, S.hcc, S.ac, S.ca, Complex.conj_ofReal]
    linear_combination S.hαβc
  · simp only [bv, inner_add_right, inner_smul_right, S.hea.o12, S.ec]; ring

lemma norm_c : ‖c‖ = 1 := by
  have h3 : ‖c‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, S.hcc]; simp
  nlinarith [norm_nonneg c]

lemma n_orth : nv a c α β ∈ (Submodule.span ℂ {e, bv a c α β})ᗮ := by
  apply mem_orth_pair
  · simp only [nv, inner_add_right, inner_smul_right, S.hea.o12, S.ec]; ring
  · simp only [nv, bv, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      S.hea.n2, S.hcc, S.ac, S.ca, Complex.conj_ofReal]
    ring

lemma P_le : Submodule.span ℂ {e, bv a c α β} ≤ A ⊔ ℂ ∙ c := by
  rw [Submodule.span_le]
  intro v hv
  rcases hv with rfl | rfl
  · exact Submodule.mem_sup_left S.he
  · exact Submodule.add_mem _ (Submodule.mem_sup_left (A.smul_mem _ S.ha))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)))

lemma A_fin : 2 ≤ Module.finrank ℂ A := S.hea.finrank S.he S.ha

lemma P_fin : 2 ≤ Module.finrank ℂ (Submodule.span ℂ {e, bv a c α β}) :=
  S.eb.finrank (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

lemma pyth {x : EuclideanSpace ℂ ι} (hx : x ∈ A) (γ : ℂ) :
    ‖x + γ • c‖ ^ 2 = ‖x‖ ^ 2 + ‖γ‖ ^ 2 := by
  have h0 : inner ℂ x (γ • c) = 0 := by
    rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal hx S.hc, mul_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sq, sq, sq, this, norm_smul, S.norm_c]
  ring


lemma round (hM : Grp M) (hAM : SUOn A ⊆ M)
    (hPM : SUOn (Submodule.span ℂ {e, bv a c α β}) ⊆ M)
    {x : EuclideanSpace ℂ ι} (hx : x ∈ A) (γ : ℂ) (hn : ‖x + γ • c‖ = 1) :
    Rch M (A ⊔ ℂ ∙ c) (x + γ • c) e ∨
      (0 < α ∧ ∃ x2 ∈ A, ∃ γ2 : ℂ, Rch M (A ⊔ ℂ ∙ c) (x + γ • c) (x2 + γ2 • c) ∧
        ‖γ2‖ ≤ ‖γ‖ - 2 * α * β ^ 2) := by
  have stepA : ∀ {y y' w : EuclideanSpace ℂ ι}, y ∈ A → y' ∈ A → ‖y‖ = ‖y'‖ → w ∈ Aᗮ →
      Rch M (A ⊔ ℂ ∙ c) (y + w) (y' + w) :=
    fun hy hy' hn hw => Rch.step le_sup_left hAM S.A_fin hy hy' hn hw
  have stepP : ∀ {y y' w : EuclideanSpace ℂ ι}, y ∈ Submodule.span ℂ {e, bv a c α β} →
      y' ∈ Submodule.span ℂ {e, bv a c α β} → ‖y‖ = ‖y'‖ →
      w ∈ (Submodule.span ℂ {e, bv a c α β})ᗮ → Rch M (A ⊔ ℂ ∙ c) (y + w) (y' + w) :=
    fun hy hy' hn hw => Rch.step S.P_le hPM S.P_fin hy hy' hn hw
  have hγc : γ • c ∈ Aᗮ := Aᗮ.smul_mem _ S.hc
  have hrg : ‖x‖ ^ 2 + ‖γ‖ ^ 2 = 1 := by rw [← S.pyth hx γ, hn]; norm_num
  have he1 : ‖e‖ = 1 := S.hea.norm1
  have heP : e ∈ Submodule.span ℂ {e, bv a c α β} := Submodule.subset_span (by simp)
  have hbP : bv a c α β ∈ Submodule.span ℂ {e, bv a c α β} := Submodule.subset_span (by simp)
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast S.hβ.ne'
  have hα1 : α ≤ 1 := by nlinarith [S.hαβ, S.hβ]
  have hβ1 : β ≤ 1 := by nlinarith [S.hαβ, S.hα]
  by_cases hγ0 : γ = 0
  · left
    subst hγ0
    have hxn : ‖x‖ = ‖e‖ := by rw [he1]; simpa using hn
    have := stepA (w := 0) hx S.he hxn (Submodule.zero_mem _)
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, r = ‖x‖ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = ‖γ‖ := ⟨_, rfl⟩
  rw [← hr, ← hg] at hrg
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg _
  have hg0 : 0 < g := by rw [hg]; exact norm_pos_iff.2 hγ0
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = γ / (g : ℂ) := ⟨_, rfl⟩
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hγω : γ = ω * g := by rw [hω, div_mul_cancel₀ _ hgc]
  have hωn : ‖ω‖ = 1 := by
    rw [hω, norm_div, Complex.norm_real, Real.norm_of_nonneg hg0.le, hg,
      div_self (norm_ne_zero_iff.2 hγ0)]
  by_cases h1 : α * g ≤ β * r
  · left
    obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = γ / β := ⟨_, rfl⟩
    have hγκ : γ = β * κ := by rw [hκ, mul_div_cancel₀ _ hβc]
    have hκn : ‖κ‖ = g / β := by
      rw [hκ, norm_div, Complex.norm_real, Real.norm_of_nonneg S.hβ.le, hg]
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (r ^ 2 - (α * g / β) ^ 2) := ⟨_, rfl⟩
    have hs2 : s ^ 2 = r ^ 2 - (α * g / β) ^ 2 := by
      rw [hs]
      apply Real.sq_sqrt
      have h3 : α * g / β ≤ r := by rw [div_le_iff₀ S.hβ]; linarith
      have h4 : 0 ≤ α * g / β := div_nonneg (mul_nonneg S.hα hg0.le) S.hβ.le
      nlinarith
    have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    have hyA : (s : ℂ) • e + ((α : ℂ) * κ) • a ∈ A := A.add_mem (A.smul_mem _ S.he) (A.smul_mem _ S.ha)
    have hyn : ‖x‖ = ‖(s : ℂ) • e + ((α : ℂ) * κ) • a‖ := by
      have h5 := S.hea.norm_sq (s : ℂ) ((α : ℂ) * κ)
      rw [norm_mul, hκn, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg S.hα,
        Real.norm_of_nonneg hs0, hs2] at h5
      have h6 : ‖(s : ℂ) • e + ((α : ℂ) * κ) • a‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [h5, ← hr]; ring
      exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h6).symm
    have r1 := stepA hx hyA hyn hγc
    have hid : (s : ℂ) • e + ((α : ℂ) * κ) • a + γ • c =
        ((s : ℂ) • e + κ • bv a c α β) + 0 := by
      rw [hγκ, bv]; module
    rw [hid] at r1
    have hpn : ‖(s : ℂ) • e + κ • bv a c α β‖ = ‖e‖ := by
      have := r1.norm; rw [hn, add_zero] at this; rw [← this, he1]
    have r2 := stepP (w := 0) (mem_pair _ _ _ _) heP hpn (Submodule.zero_mem _)
    simp only [add_zero] at r2
    exact Rch.trans hM r1 (by simpa only [add_zero] using r2)
  push Not at h1
  have hα0 : 0 < α := by
    rcases S.hα.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; nlinarith [S.hβ]
  obtain ⟨L, hL⟩ : ∃ L, L = α * r + β * g := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = α * g - β * r := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; nlinarith [S.hα, S.hβ]
  have hD0 : 0 < D := by rw [hD]; linarith
  have hyA : (ω * (r : ℂ)) • a ∈ A := A.smul_mem _ S.ha
  have hyn : ‖x‖ = ‖(ω * (r : ℂ)) • a‖ := by
    rw [norm_smul, norm_mul, hωn, Complex.norm_real, Real.norm_of_nonneg hr0, S.hea.norm2, hr]
    ring
  have r1 := stepA hx hyA hyn hγc
  have hid : (ω * (r : ℂ)) • a + γ • c =
      (ω * (L : ℂ)) • bv a c α β + (ω * (D : ℂ)) • nv a c α β := by
    rw [hγω, bv, nv, hL, hD]
    push_cast
    linear_combination (norm := module) (-(ω * (r : ℂ))) • (S.hαβc • a) -
      (ω * (g : ℂ)) • (S.hαβc • c)
  rw [hid] at r1
  have hw : (ω * (D : ℂ)) • nv a c α β ∈ (Submodule.span ℂ {e, bv a c α β})ᗮ :=
    Submodule.smul_mem _ _ S.n_orth
  have hpP : (ω * (L : ℂ)) • bv a c α β ∈ Submodule.span ℂ {e, bv a c α β} :=
    Submodule.smul_mem _ _ hbP
  have hLn : ‖(ω * (L : ℂ)) • bv a c α β‖ = L := by
    rw [norm_smul, norm_mul, hωn, Complex.norm_real, Real.norm_of_nonneg hL0, S.eb.norm2]; ring
  by_cases h2 : α * D ≤ β * L
  · left
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = α * D / β := ⟨_, rfl⟩
    have hmβ : β * m = α * D := by rw [hm]; field_simp [S.hβ.ne']
    have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg (mul_nonneg S.hα hD0.le) S.hβ.le
    have hmL : m ≤ L := by rw [hm, div_le_iff₀ S.hβ]; linarith
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (L ^ 2 - m ^ 2) := ⟨_, rfl⟩
    have hs2 : s ^ 2 = L ^ 2 - m ^ 2 := by rw [hs]; exact Real.sq_sqrt (by nlinarith)
    have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    have hp'n : ‖(ω * (L : ℂ)) • bv a c α β‖ =
        ‖(ω * (s : ℂ)) • e + (-(ω * (m : ℂ))) • bv a c α β‖ := by
      have h5 := S.eb.norm_sq (ω * (s : ℂ)) (-(ω * (m : ℂ)))
      rw [norm_neg, norm_mul, norm_mul, hωn, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hs0, Real.norm_of_nonneg hm0, one_mul, one_mul, hs2] at h5
      have h6 : ‖(ω * (s : ℂ)) • e + (-(ω * (m : ℂ))) • bv a c α β‖ ^ 2 = L ^ 2 := by
        rw [h5]; ring
      rw [hLn]
      exact ((sq_eq_sq₀ hL0 (norm_nonneg _)).1 h6.symm)
    have r2 := stepP hpP (mem_pair _ _ _ _) hp'n hw
    have hmβc : (β : ℂ) * m = α * D := by exact_mod_cast hmβ
    have hid2 : (ω * (s : ℂ)) • e + (-(ω * (m : ℂ))) • bv a c α β + (ω * (D : ℂ)) • nv a c α β =
        ((ω * (s : ℂ)) • e + (ω * (-(m * α) - β * D) : ℂ) • a) + 0 := by
      rw [bv, nv]
      linear_combination (norm := module) (-ω) • (hmβc • c)
    rw [hid2] at r2
    have r12 := Rch.trans hM r1 r2
    have hvA : (ω * (s : ℂ)) • e + (ω * (-(m * α) - β * D) : ℂ) • a ∈ A :=
      A.add_mem (A.smul_mem _ S.he) (A.smul_mem _ S.ha)
    have hvn : ‖(ω * (s : ℂ)) • e + (ω * (-(m * α) - β * D) : ℂ) • a‖ = ‖e‖ := by
      have := r12.norm; rw [hn, add_zero] at this; rw [← this, he1]
    have r3 := stepA (w := 0) hvA S.he hvn (Submodule.zero_mem _)
    simp only [add_zero] at r3
    exact Rch.trans hM r12 (by simpa only [add_zero] using r3)
  · right
    push Not at h2
    refine ⟨hα0, (ω * (-(L * α) - D * β) : ℂ) • a, A.smul_mem _ S.ha,
      ω * (D * α - L * β), ?_, ?_⟩
    · have hp'n : ‖(ω * (L : ℂ)) • bv a c α β‖ = ‖(-(ω * (L : ℂ))) • bv a c α β‖ := by
        rw [neg_smul, norm_neg]
      have r2 := stepP hpP (Submodule.smul_mem _ _ hbP) hp'n hw
      have hid2 : (-(ω * (L : ℂ))) • bv a c α β + (ω * (D : ℂ)) • nv a c α β =
          (ω * (-(L * α) - D * β) : ℂ) • a + (ω * (D * α - L * β)) • c := by
        rw [bv, nv]; module
      rw [hid2] at r2
      exact Rch.trans hM r1 r2
    · have hpos : 0 ≤ D * α - L * β := by nlinarith
      rw [show (ω * ((D : ℂ) * α - L * β)) = ω * ((D * α - L * β : ℝ) : ℂ) by push_cast; ring,
        norm_mul, hωn, Complex.norm_real, Real.norm_of_nonneg hpos, one_mul, ← hg, hD, hL]
      have hgr : 1 ≤ g + r := by nlinarith [mul_nonneg hg0.le hr0]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hα1) (sq_nonneg β)) hg0.le,
        mul_nonneg (mul_nonneg (mul_nonneg S.hα S.hβ.le) (sub_nonneg.2 hβ1)) hr0,
        mul_nonneg (mul_nonneg S.hα (sq_nonneg β)) (sub_nonneg.2 hgr), S.hαβ]


lemma reach (hM : Grp M) (hAM : SUOn A ⊆ M)
    (hPM : SUOn (Submodule.span ℂ {e, bv a c α β}) ⊆ M) {x : EuclideanSpace ℂ ι} (hx : x ∈ A)
    (γ : ℂ) (hn : ‖x + γ • c‖ = 1) : Rch M (A ⊔ ℂ ∙ c) (x + γ • c) e := by
  by_cases hα0 : α = 0
  · rcases S.round hM hAM hPM hx γ hn with h | ⟨h, -⟩
    · exact h
    · exact absurd hα0 h.ne'
  have hα : 0 < α := lt_of_le_of_ne S.hα (Ne.symm hα0)
  have hδ : 0 < 2 * α * β ^ 2 := by have := S.hβ; positivity
  suffices H : ∀ k : ℕ, ∀ x ∈ A, ∀ γ : ℂ, ‖x + γ • c‖ = 1 → ‖γ‖ ≤ k * (2 * α * β ^ 2) →
      Rch M (A ⊔ ℂ ∙ c) (x + γ • c) e by
    obtain ⟨k, hk⟩ := exists_nat_ge (‖γ‖ / (2 * α * β ^ 2))
    exact H k x hx γ hn (by rwa [div_le_iff₀ hδ] at hk)
  intro k
  induction k with
  | zero =>
    intro x hx γ hn hγ
    rcases S.round hM hAM hPM hx γ hn with h | ⟨-, x2, -, γ2, -, hb⟩
    · exact h
    · exfalso
      have := norm_nonneg γ2
      push_cast at hγ
      linarith
  | succ k ih =>
    intro x hx γ hn hγ
    rcases S.round hM hAM hPM hx γ hn with h | ⟨-, x2, hx2, γ2, hr, hb⟩
    · exact h
    · have hn2 : ‖x2 + γ2 • c‖ = 1 := by rw [← hr.norm, hn]
      refine Rch.trans hM hr (ih x2 hx2 γ2 hn2 ?_)
      push_cast at hγ
      linarith

lemma lemmaC (hM : Grp M) (hAM : SUOn A ⊆ M)
    (hPM : SUOn (Submodule.span ℂ {e, bv a c α β}) ⊆ M) : SUOn (A ⊔ ℂ ∙ c) ⊆ M := by
  intro U hU
  have hcW : c ∈ A ⊔ ℂ ∙ c := Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
  have huW := SUOn_maps hU hcW
  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 huW
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hun : ‖x + γ • c‖ = 1 := by rw [hxz, norm_act (SUOn_U hU), S.norm_c]
  have h1 := S.reach hM hAM hPM hx γ hun
  have h2 := S.reach hM hAM hPM A.zero_mem 1 (by simp [S.norm_c])
  rw [zero_add, one_smul] at h2
  obtain ⟨g, hgM, hgS, hgu⟩ := Rch.trans hM h1 (Rch.symm hM h2)
  rw [hxz, ← act_mul] at hgu
  have hV := stab S.hcc S.hc (SUOn_mul hgS hU) hgu
  have e : U = gᴴ * (g * U) := by
    rw [← Matrix.mul_assoc, unitary_star_mul (SUOn_U hgS), Matrix.one_mul]
  rw [e]
  exact hM.mul (hM.star hgM) (hAM hV)

end CSetup

/-! ### Two subspaces with nonzero intersection -/

lemma lemmaD (hM : Grp M) (B : Submodule ℂ (EuclideanSpace ℂ ι)) (hBM : SUOn B ⊆ M) :
    ∀ n : ℕ, ∀ A : Submodule ℂ (EuclideanSpace ℂ ι),
      Module.finrank ℂ (A ⊔ B : Submodule ℂ _) - Module.finrank ℂ A = n → A ⊓ B ≠ ⊥ →
      SUOn A ⊆ M → SUOn (A ⊔ B) ⊆ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hAB hAM
  by_cases hBA : B ≤ A
  · rw [sup_eq_left.2 hBA]; exact hAM
  by_cases hAB' : A ≤ B
  · rw [sup_eq_right.2 hAB']; exact hBM
  -- the unit vector `e` in `A ⊓ B`
  obtain ⟨e0, he0, he00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAB
  set K := A ⊓ B with hK
  obtain ⟨e, he⟩ : ∃ e, e = ((‖e0‖ : ℂ)⁻¹) • e0 := ⟨_, rfl⟩
  have heK : e ∈ K := by rw [he]; exact K.smul_mem _ he0
  have hee : inner ℂ e e = 1 := by rw [he]; exact inner_normalize he00
  have heA : e ∈ A := (Submodule.mem_inf.1 heK).1
  have heB : e ∈ B := (Submodule.mem_inf.1 heK).2
  -- the unit vector `b` in `B ⊖ K`
  have hKB : K ≤ B := inf_le_right
  have hne : Kᗮ ⊓ B ≠ ⊥ := by
    intro h
    have := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKB
    rw [h, sup_bot_eq] at this
    exact hBA (this ▸ inf_le_left)
  obtain ⟨b0, hb0, hb00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨b, hb⟩ : ∃ b, b = ((‖b0‖ : ℂ)⁻¹) • b0 := ⟨_, rfl⟩
  have hbb : inner ℂ b b = 1 := by rw [hb]; exact inner_normalize hb00
  have hbB : b ∈ B := by rw [hb]; exact B.smul_mem _ (Submodule.mem_inf.1 hb0).2
  have hbK : b ∈ Kᗮ := by rw [hb]; exact Kᗮ.smul_mem _ (Submodule.mem_inf.1 hb0).1
  have heb : inner ℂ e b = 0 := Submodule.inner_right_of_mem_orthogonal heK hbK
  have hbA : b ∉ A := by
    intro h
    have : inner ℂ b b = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.mem_inf.2 ⟨h, hbB⟩) hbK
    rw [hbb] at this; exact one_ne_zero this
  -- decompose `b = bA + bP`
  obtain ⟨bA, hbAd⟩ : ∃ bA, bA = A.starProjection b := ⟨_, rfl⟩
  have hbAA : bA ∈ A := by rw [hbAd]; exact A.starProjection_apply_mem b
  obtain ⟨bP, hbPd⟩ : ∃ bP, bP = b - bA := ⟨_, rfl⟩
  have hbPA : bP ∈ Aᗮ := by rw [hbPd, hbAd]; exact A.sub_starProjection_mem_orthogonal b
  have hbP0 : bP ≠ 0 := by
    intro h; apply hbA
    have : b = bA := by rw [← sub_eq_zero, ← hbPd, h]
    rw [this]; exact hbAA
  obtain ⟨α, hα⟩ : ∃ α, α = ‖bA‖ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ‖bP‖ := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; exact norm_pos_iff.2 hbP0
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hb1 : ‖b‖ = 1 := by
    have h3 : ‖b‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, hbb]; simp
    nlinarith [norm_nonneg b]
  have hαβ : α ^ 2 + β ^ 2 = 1 := by
    have h0 : inner ℂ bA bP = 0 := Submodule.inner_right_of_mem_orthogonal hbAA hbPA
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [hbPd, add_sub_cancel, hb1] at this
    rw [hα, hβ, hbPd]; nlinarith [this]
  obtain ⟨c, hcd⟩ : ∃ c, c = ((β : ℂ)⁻¹) • bP := ⟨_, rfl⟩
  have hcA : c ∈ Aᗮ := by rw [hcd]; exact Aᗮ.smul_mem _ hbPA
  have hcc : inner ℂ c c = 1 := by rw [hcd, hβ]; exact inner_normalize hbP0
  have hbPc : bP = (β : ℂ) • c := by rw [hcd, smul_smul, mul_inv_cancel₀ hβc, one_smul]
  have hA2 : 2 ≤ Module.finrank ℂ A := by
    by_contra hlt
    push Not at hlt
    have he0 : e ≠ 0 := by rintro rfl; simp at hee
    have hle : (ℂ ∙ e) ≤ A := (Submodule.span_singleton_le_iff_mem _ _).2 heA
    have hfe := finrank_span_singleton (K := ℂ) he0
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    apply hAB'
    rw [← heq]
    exact (Submodule.span_singleton_le_iff_mem _ _).2 heB
  obtain ⟨a, haA, hea, hbAa⟩ : ∃ a ∈ A, ON e a ∧ bA = (α : ℂ) • a := by
    by_cases hbA0 : bA = 0
    · obtain ⟨a, haA, haa, hea⟩ := exists_perp hA2 heA
      refine ⟨a, haA, ⟨hee, haa, hea⟩, ?_⟩
      rw [hbA0, hα, hbA0, norm_zero]; simp
    · refine ⟨((α : ℂ)⁻¹) • bA, A.smul_mem _ hbAA, ⟨hee, ?_, ?_⟩, ?_⟩
      · rw [hα]; exact inner_normalize hbA0
      · have h1 : inner ℂ e bA = 0 := by
          have : bA = b - bP := by rw [hbPd, sub_sub_cancel]
          rw [this, inner_sub_right, heb, Submodule.inner_right_of_mem_orthogonal heA hbPA,
            sub_zero]
        rw [inner_smul_right, h1, mul_zero]
      · have hαc : (α : ℂ) ≠ 0 := by rw [hα]; exact_mod_cast norm_ne_zero_iff.2 hbA0
        rw [smul_smul, mul_inv_cancel₀ hαc, one_smul]
  have hbv : bv a c α β = b := by
    rw [bv, ← hbAa, ← hbPc, hbPd, add_sub_cancel]
  have S : CSetup A e a c α β :=
    ⟨heA, haA, hcA, hea, hcc, by rw [hα]; exact norm_nonneg _, hβ0, hαβ⟩
  have hPM : SUOn (Submodule.span ℂ {e, bv a c α β}) ⊆ M := by
    refine (SUOn_mono ?_).trans hBM
    rw [hbv, Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact heB
    · exact hbB
  have hA'M := S.lemmaC hM hAM hPM
  have hcAB : c ∈ A ⊔ B := by
    rw [hcd, hbPd]
    exact (A ⊔ B).smul_mem _ ((A ⊔ B).sub_mem (Submodule.mem_sup_right hbB)
      (Submodule.mem_sup_left hbAA))
  have hA'B : A ⊔ ℂ ∙ c ⊔ B = A ⊔ B := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 hcAB))
        le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hlt : A < A ⊔ ℂ ∙ c := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hcA' : c ∈ A := by rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
    have : inner ℂ c c = 0 := Submodule.inner_right_of_mem_orthogonal hcA' hcA
    rw [hcc] at this; exact one_ne_zero this
  have hf1 := Submodule.finrank_lt_finrank_of_lt hlt
  have hf2 : Module.finrank ℂ (A ⊔ ℂ ∙ c : Submodule ℂ _) ≤ Module.finrank ℂ (A ⊔ B : Submodule ℂ _) :=
    Submodule.finrank_mono (hA'B ▸ le_sup_left)
  have hK' : (A ⊔ ℂ ∙ c) ⊓ B ≠ ⊥ := by
    intro h; apply hAB
    exact le_bot_iff.1 (h ▸ inf_le_inf_right B le_sup_left)
  have := ih _ (by rw [← hn, hA'B]; omega) (A ⊔ ℂ ∙ c) rfl hK' hA'M
  rwa [hA'B] at this

/-! ### Closedness and the dense-generation wrapper -/

lemma SUOn_closed (W : Submodule ℂ (EuclideanSpace ℂ ι)) : IsClosed (SUOn W) := by
  have h1 : IsClosed {U : Matrix ι ι ℂ | U * star U = 1} :=
    isClosed_eq (continuous_id.mul continuous_star) continuous_const
  have h2 : IsClosed {U : Matrix ι ι ℂ | U.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have h3 : ∀ v : EuclideanSpace ℂ ι, IsClosed {U : Matrix ι ι ℂ | act U v = v} := by
    intro v
    refine isClosed_eq ?_ continuous_const
    have : (fun U : Matrix ι ι ℂ => act U v) = fun U => toLp 2 (U *ᵥ ofLp v) := rfl
    rw [this]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)
  have e : SUOn W = ({U : Matrix ι ι ℂ | U * star U = 1} ∩ {U | U.det = 1}) ∩
      ⋂ v ∈ Wᗮ, {U : Matrix ι ι ℂ | act U v = v} := by
    ext U
    simp only [mem_SUOn, mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter]
  rw [e]
  exact (h1.inter h2).inter (isClosed_biInter fun v _ => h3 v)

/-- The submonoid of matrices underlying `denseGen`. -/
noncomputable def S0 (G : Set (Matrix.unitaryGroup ι ℂ)) : Submonoid (Matrix ι ι ℂ) :=
  (Submonoid.closure G).map (Matrix.unitaryGroup ι ℂ).subtype

lemma denseGen_eq (G : Set (Matrix.unitaryGroup ι ℂ)) :
    denseGen G = ((S0 G).topologicalClosure : Set (Matrix ι ι ℂ)) := by
  rw [Submonoid.coe_topologicalClosure, denseGen, S0, Submonoid.coe_map]
  rfl

lemma denseGen_mono {G G' : Set (Matrix.unitaryGroup ι ℂ)} (h : G ⊆ G') :
    denseGen G ⊆ denseGen G' :=
  closure_mono (Set.image_mono (Submonoid.closure_mono h))

end BaconThesis.Universality.Sol431

open BaconThesis.Universality BaconThesis.Universality.Sol431 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W₁ W₂ : Submodule ℂ (EuclideanSpace ℂ ι)) (hW : W₁ ⊓ W₂ ≠ ⊥)
    (O₁ O₂ : Set (Matrix.unitaryGroup ι ℂ))
    (h₁ : SUOn W₁ ⊆ denseGen O₁) (h₂ : SUOn W₂ ⊆ denseGen O₂) :
    SUOn (W₁ ⊔ W₂) ⊆ denseGen (O₁ ∪ O₂) ∧
      (denseGen O₁ ⊆ SUOn W₁ → denseGen O₂ ⊆ SUOn W₂ →
        denseGen (O₁ ∪ O₂) = SUOn (W₁ ⊔ W₂)) := by
  -- part 1
  set M := Submonoid.closure (SUOn W₁ ∪ SUOn W₂) with hMd
  have hM : Grp (M : Set (Matrix ι ι ℂ)) := by
    refine ⟨M.one_mem, fun hU hV => M.mul_mem hU hV, fun {U} hU => ?_⟩
    induction hU using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Submonoid.subset_closure (Or.inl (SUOn_star hx))
      · exact Submonoid.subset_closure (Or.inr (SUOn_star hx))
    | one => rw [conjTranspose_one]; exact M.one_mem
    | mul x y _ _ hx hy => rw [conjTranspose_mul]; exact M.mul_mem hy hx
  have hMD : (M : Set (Matrix ι ι ℂ)) ⊆ denseGen (O₁ ∪ O₂) := by
    rw [denseGen_eq]
    show M ≤ (S0 (O₁ ∪ O₂)).topologicalClosure
    rw [Submonoid.closure_le]
    rintro U (hU | hU)
    · have := denseGen_mono (Set.subset_union_left (t := O₂)) (h₁ hU)
      rwa [denseGen_eq] at this
    · have := denseGen_mono (Set.subset_union_right (s := O₁)) (h₂ hU)
      rwa [denseGen_eq] at this
  have part1 : SUOn (W₁ ⊔ W₂) ⊆ denseGen (O₁ ∪ O₂) := by
    refine Set.Subset.trans ?_ hMD
    exact lemmaD hM W₂ (fun U hU => Submonoid.subset_closure (Or.inr hU)) _ W₁ rfl hW
      (fun U hU => Submonoid.subset_closure (Or.inl hU))
  refine ⟨part1, fun hd₁ hd₂ => Set.Subset.antisymm ?_ part1⟩
  -- part 2
  have hgen : ∀ u ∈ O₁ ∪ O₂, (u : Matrix ι ι ℂ) ∈ SUOn (W₁ ⊔ W₂) := by
    rintro u (hu | hu)
    · exact SUOn_mono le_sup_left (hd₁ (subset_closure ⟨u, Submonoid.subset_closure hu, rfl⟩))
    · exact SUOn_mono le_sup_right (hd₂ (subset_closure ⟨u, Submonoid.subset_closure hu, rfl⟩))
  have hsub : Subtype.val '' (Submonoid.closure (O₁ ∪ O₂) : Set (Matrix.unitaryGroup ι ℂ)) ⊆
      SUOn (W₁ ⊔ W₂) := by
    rintro _ ⟨u, hu, rfl⟩
    induction hu using Submonoid.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact SUOn_one _
    | mul x y _ _ hx hy => exact SUOn_mul hx hy
  exact (SUOn_closed _).closure_subset_iff.2 hsub
