-- Prove2me | solution 1 for CuspForm.isReduced_heckeAlgebra_of_primeFactors_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e2e634bc-60f5-5f4b-b801-19db5fd51309

import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset

set_option autoImplicit false

noncomputable section

namespace H6

section LinearAlgebra

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]

theorem adjoin_actsAsScalar {G : Set (Module.End K E)} {W : Submodule K E}
    (hG : ∀ g ∈ G, ∃ c : K, ∀ v ∈ W, g v = c • v)
    {x : Module.End K E} (hx : x ∈ Algebra.adjoin ℤ G) :
    ∃ c : K, ∀ v ∈ W, x v = c • v := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg => exact hG g hg
  | algebraMap r =>
      refine ⟨(r : K), fun v _ => ?_⟩
      simp only [algebraMap_int_eq, eq_intCast, Module.End.intCast_apply]
      exact (Int.cast_smul_eq_zsmul K r v).symm
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx; obtain ⟨d, hd⟩ := ihy
      exact ⟨c + d, fun v hv => by
        simp only [LinearMap.add_apply, hc v hv, hd v hv, add_smul]⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx; obtain ⟨d, hd⟩ := ihy
      refine ⟨c * d, fun v hv => ?_⟩
      have : (x * y) v = x (y v) := rfl
      rw [this, hd v hv, map_smul, hc v hv, smul_smul, mul_comm d c]

theorem isReduced_adjoin {ι : Sort*} {G : Set (Module.End K E)} {W : ι → Submodule K E}
    (hW : (⨆ i, W i) = ⊤)
    (hG : ∀ g ∈ G, ∀ i, ∃ c : K, ∀ v ∈ W i, g v = c • v) :
    IsReduced (Algebra.adjoin ℤ G) := by
  constructor
  rintro ⟨x, hx⟩ ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    have h := congrArg (Subtype.val) hn
    simpa using h
  have hker : ∀ i, W i ≤ LinearMap.ker x := by
    intro i v hv
    obtain ⟨c, hc⟩ := adjoin_actsAsScalar (fun g hg => hG g hg i) hx
    have hpow : ∀ m : ℕ, (x ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          have h1 : (x ^ (m + 1)) v = (x ^ m) (x v) := by
            rw [pow_succ]; rfl
          rw [h1, hc v hv, map_smul, ih, smul_smul, pow_succ, mul_comm c (c ^ m)]
    have h0 : c ^ n • v = 0 := by
      rw [← hpow n, hxn]; rfl
    rcases smul_eq_zero.mp h0 with h | h
    · have hc0 : c = 0 := IsNilpotent.eq_zero ⟨n, h⟩
      have : x v = 0 := by rw [hc v hv, hc0, zero_smul]
      exact this
    · show x v = 0
      rw [h, map_zero]
  have htop : ⊤ ≤ LinearMap.ker x := hW ▸ iSup_le hker
  exact Subtype.ext (LinearMap.ker_eq_top.mp (top_le_iff.mp htop))

end LinearAlgebra

section Symmetric

open Module LinearMap

theorem isReduced_adjoin_of_isSymmetric_of_commute
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {G : Set (Module.End ℂ E)}
    (hsym : ∀ g ∈ G, LinearMap.IsSymmetric (g : E →ₗ[ℂ] E))
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g') :
    IsReduced (Algebra.adjoin ℤ G) := by
  have hkey :
      (⨆ χ : G → ℂ, ⨅ g : G, Module.End.eigenspace (g : Module.End ℂ E) (χ g)) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
      (T := fun g : G => (g : Module.End ℂ E))
      (fun g => hsym g g.2) (fun i j _ => hcomm i i.2 j j.2)
  refine isReduced_adjoin hkey ?_
  intro g hg χ
  refine ⟨χ ⟨g, hg⟩, fun v hv => ?_⟩
  have hmem := (Submodule.mem_iInf
    (fun g' : G => Module.End.eigenspace (g' : Module.End ℂ E) (χ g'))).mp hv ⟨g, hg⟩
  exact Module.End.mem_eigenspace_iff.mp hmem

theorem isReduced_adjoin_of_core
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) {G : Set (Module.End ℂ V)}
    (hsym : ∀ g ∈ G, ∀ v w : V, c.inner (g v) w = c.inner v (g w))
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g') :
    IsReduced (Algebra.adjoin ℤ G) := by
  letI hc : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := hc.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := .ofCore _
  exact isReduced_adjoin_of_isSymmetric_of_commute (fun g hg v w => hsym g hg v w) hcomm

end Symmetric

section Glue

open CongruenceSubgroup

theorem heckeAlgebra_isReduced_of_core
    (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)
    [FiniteDimensional ℂ (CuspForm (Gamma0 N) k)]
    (c : InnerProductSpace.Core ℂ (CuspForm (Gamma0 N) k))
    (hsym : ∀ T ∈ CuspForm.heckeGenerators N k S,
      ∀ v w : CuspForm (Gamma0 N) k, c.inner (T v) w = c.inner v (T w)) :
    IsReduced (CuspForm.heckeAlgebra N k S) :=
  isReduced_adjoin_of_core c hsym
    (fun _ hg _ hg' => CuspForm.commute_of_mem_heckeGenerators hg hg')

theorem heckeAlgebra_isReduced_of_core_anemic
    (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [FiniteDimensional ℂ (CuspForm (Gamma0 N) k)]
    (c : InnerProductSpace.Core ℂ (CuspForm (Gamma0 N) k))
    (hsymT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      ∀ v w : CuspForm (Gamma0 N) k,
        c.inner (CuspForm.heckeTLin k hℓ hℓN v) w = c.inner v (CuspForm.heckeTLin k hℓ hℓN w)) :
    IsReduced (CuspForm.heckeAlgebra N k S) := by
  refine heckeAlgebra_isReduced_of_core N k S c ?_
  rintro T (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
  · exact hsymT ℓ hℓ hℓN hℓS
  · exact absurd (hNS q hq hqN) hqS

end Glue

section Definiteness

open MeasureTheory

theorem cuspForm_eq_zero_of_ae_restrict_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    [Measure.IsOpenPosMeasure (volume : Measure UpperHalfPlane)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    {U D : Set UpperHalfPlane} (hU : IsOpen U) (hne : U.Nonempty) (hUD : U ⊆ D)
    (hae : ∀ᵐ τ ∂(volume.restrict D), f τ = 0) :
    f = 0 := by
  have hae' : ⇑f =ᵐ[volume.restrict U] (0 : UpperHalfPlane → ℂ) :=
    ae_restrict_of_ae_restrict_of_subset hUD hae
  have heq : Set.EqOn ⇑f 0 U :=
    Measure.eqOn_open_of_ae_eq hae' hU
      (ModularFormClass.continuous f).continuousOn continuousOn_const
  obtain ⟨τ₀, hτ₀⟩ := hne
  have hfreq : ∃ᶠ z in nhdsWithin τ₀ {τ₀}ᶜ, f z = 0 := by
    have hev : ∀ᶠ z in nhds τ₀, f z = 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hτ₀) fun z hz => heq hz
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  have h0 : ⇑f = 0 := UpperHalfPlane.eq_zero_of_frequently (ModularFormClass.holo f) hfreq
  exact DFunLike.coe_injective (by simpa using h0)

end Definiteness

section HeckeCosets

open ModularForm CongruenceSubgroup
open scoped MatrixGroups

theorem heckeDiagMatrix_eq_mul_heckeMatrix_mul {p N : ℕ} (hp : p ≠ 0)
    (hpN : Nat.Coprime p N) :
    ∃ γ₁ γ₂ : SL(2, ℤ), γ₁ ∈ Gamma0 N ∧ γ₂ ∈ Gamma0 N ∧
      heckeDiagMatrix p =
        Matrix.SpecialLinearGroup.mapGL ℝ γ₁ * heckeMatrix p 0 *
          Matrix.SpecialLinearGroup.mapGL ℝ γ₂ := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hpN)

  set d : ℤ := u with hd
  set b : ℤ := -v with hb
  have hBez : d * p - b * N = 1 := by
    rw [hd, hb]; linarith [huv]
  have hdet₁ : Matrix.det !![(p : ℤ), b; (N : ℤ), d] = 1 := by
    rw [Matrix.det_fin_two_of]; linarith [hBez]
  have hdet₂ : Matrix.det !![d * p, -b; -(N : ℤ), 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linarith [hBez]
  refine ⟨⟨_, hdet₁⟩, ⟨_, hdet₂⟩, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    simp
  · rw [Gamma0_mem]
    show ((-(N : ℤ) : ℤ) : ZMod N) = 0
    simp
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    rw [val_heckeDiagMatrix hp, val_heckeMatrix hp]
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have hR : (d : ℝ) * p - b * N = 1 := by exact_mod_cast congrArg (Int.cast (R := ℝ)) hBez
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [hR]

theorem heckeMatrix_mul_mem_coset {p N : ℕ} (hp : p.Prime) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      ((∃ j : ℕ, j < p ∧
          heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ =
            Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeMatrix p j) ∨
        heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ =
          Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeDiagMatrix p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : Fact p.Prime := ⟨hp⟩
  set a : ℤ := γ.1 0 0 with ha
  set b : ℤ := γ.1 0 1 with hb
  set c : ℤ := γ.1 1 0 with hc
  set d : ℤ := γ.1 1 1 with hd
  have hγdet : a * d - b * c = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hγval : (γ.1 : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  have hcN : ((c : ZMod N)) = 0 := by
    rw [Gamma0_mem] at hγ
    exact_mod_cast hγ
  by_cases hpa : (p : ℤ) ∣ a
  ·
    obtain ⟨a', ha'⟩ := hpa
    have hdet : Matrix.det !![a', b; c, (p : ℤ) * d] = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hγdet - d * ha'
    refine ⟨⟨_, hdet⟩, ?_, Or.inr ?_⟩
    · rw [Gamma0_mem]
      show ((c : ZMod N)) = 0
      exact hcN
    · apply Units.ext
      have haR : (a : ℝ) = p * a' := by exact_mod_cast congrArg (Int.cast (R := ℝ)) ha'
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, val_heckeMatrix hp0, val_heckeDiagMatrix hp0,
          Matrix.SpecialLinearGroup.mapGL_coe_matrix, hγval,
          Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
        nlinarith [haR]
  ·
    have haZ : (a : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    set jz : ZMod p := (b : ZMod p) * (a : ZMod p)⁻¹ with hjz
    set j : ℕ := jz.val with hj
    have hjp : j < p := ZMod.val_lt jz
    have hjcast : ((j : ℕ) : ZMod p) = jz := ZMod.natCast_zmod_val jz
    have hjmul : (a : ZMod p) * jz = (b : ZMod p) := by
      calc (a : ZMod p) * ((b : ZMod p) * (a : ZMod p)⁻¹)
          = (b : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) := by ring
        _ = (b : ZMod p) := by rw [mul_inv_cancel₀ haZ, mul_one]
    have hdvd : (p : ℤ) ∣ b - a * j := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjcast, hjmul, sub_self]
    obtain ⟨e, he⟩ := hdvd
    have hep : e * p = b - a * j := by linear_combination -he
    have hdet : Matrix.det !![a, e; (p : ℤ) * c, d - c * j] = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hγdet - c * hep
    refine ⟨⟨_, hdet⟩, ?_, Or.inl ⟨j, hjp, ?_⟩⟩
    · rw [Gamma0_mem]
      show (((p : ℤ) * c : ℤ) : ZMod N) = 0
      push_cast
      rw [hcN]
      ring
    · apply Units.ext
      have hepR : (e : ℝ) * p = (b : ℝ) - a * j := by
        exact_mod_cast congrArg (Int.cast (R := ℝ)) hep
      ext i j'
      fin_cases i <;> fin_cases j' <;>
        simp [Units.val_mul, val_heckeMatrix hp0,
          Matrix.SpecialLinearGroup.mapGL_coe_matrix, hγval,
          Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
        nlinarith [hepR]

theorem heckeMatrix_coset_inj {p : ℕ} (hp : p ≠ 0) {j j' : ℕ} (hj : j < p) (hj' : j' < p)
    (δ : SL(2, ℤ))
    (h : Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeMatrix p j = heckeMatrix p j') :
    j = j' := by
  set u : ℤ := δ.1 0 0 with hu
  set v : ℤ := δ.1 0 1 with hv
  set w : ℤ := δ.1 1 0 with hw
  set x : ℤ := δ.1 1 1 with hx
  have hδval : (δ.1 : Matrix (Fin 2) (Fin 2) ℤ) = !![u, v; w, x] := by
    ext i j₀; fin_cases i <;> fin_cases j₀ <;> simp [hu, hv, hw, hx]
  have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ δ).val * (heckeMatrix p j).val :
      Matrix (Fin 2) (Fin 2) ℝ) = (heckeMatrix p j').val := by
    rw [← Units.val_mul, h]
  have h00 : (u : ℝ) = 1 := by
    have := congrFun (congrFun hm 0) 0
    simpa [val_heckeMatrix hp, Matrix.SpecialLinearGroup.mapGL_coe_matrix, hδval,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (u : ℝ) * j + v * p = j' := by
    have := congrFun (congrFun hm 0) 1
    simpa [val_heckeMatrix hp, Matrix.SpecialLinearGroup.mapGL_coe_matrix, hδval,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hu1 : u = 1 := by exact_mod_cast h00
  have hZ : (j : ℤ) + v * p = j' := by
    have : (1 : ℝ) * j + v * p = j' := by rw [← h00]; exact h01
    exact_mod_cast (by linarith [this] : ((j : ℝ) + v * p : ℝ) = j')
  have hjZ : (j : ℤ) < p := by exact_mod_cast hj
  have hj'Z : (j' : ℤ) < p := by exact_mod_cast hj'
  have hjnn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hj'nn : (0 : ℤ) ≤ j' := Int.natCast_nonneg j'
  have hppos : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hvp_lt : v * p < p := by linarith
  have hvp_gt : -(p : ℤ) < v * p := by linarith
  have hv0 : v = 0 := by
    by_contra hv'
    rcases lt_or_gt_of_ne hv' with hneg | hpos
    · nlinarith
    · nlinarith
  have : (j : ℤ) = j' := by rw [hv0] at hZ; linarith
  exact_mod_cast this

theorem heckeDiagMatrix_ne_mul_heckeMatrix {p : ℕ} (hp : 1 < p) (j : ℕ)
    (δ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeMatrix p j ≠ heckeDiagMatrix p := by
  intro h
  have hp0 : p ≠ 0 := by omega
  set u : ℤ := δ.1 0 0 with hu
  set v : ℤ := δ.1 0 1 with hv
  set w : ℤ := δ.1 1 0 with hw
  set x : ℤ := δ.1 1 1 with hx
  have hδval : (δ.1 : Matrix (Fin 2) (Fin 2) ℤ) = !![u, v; w, x] := by
    ext i j₀; fin_cases i <;> fin_cases j₀ <;> simp [hu, hv, hw, hx]
  have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ δ).val * (heckeMatrix p j).val :
      Matrix (Fin 2) (Fin 2) ℝ) = (heckeDiagMatrix p).val := by
    rw [← Units.val_mul, h]
  have h10 : (w : ℝ) = 0 := by
    have := congrFun (congrFun hm 1) 0
    simpa [val_heckeMatrix hp0, val_heckeDiagMatrix hp0,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, hδval,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (w : ℝ) * j + x * p = 1 := by
    have := congrFun (congrFun hm 1) 1
    simpa [val_heckeMatrix hp0, val_heckeDiagMatrix hp0,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, hδval,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hw0 : w = 0 := by exact_mod_cast h10
  have hxZ : x * (p : ℤ) = 1 := by
    have : (0 : ℝ) * j + x * p = 1 := by rw [← h10]; exact h11
    exact_mod_cast (by linarith [this] : ((x : ℝ) * p : ℝ) = 1)
  have hpZ : (1 : ℤ) < p := by exact_mod_cast hp
  have hdvd : (p : ℤ) ∣ 1 := ⟨x, by linear_combination -hxZ⟩
  have := Int.le_of_dvd one_pos hdvd
  omega

end HeckeCosets

section Unfold

open scoped MatrixGroups

variable {Γ Δ : Subgroup SL(2, ℤ)}

def unfoldRep (Γ Δ : Subgroup SL(2, ℤ)) (q : Γ ⧸ Δ.subgroupOf Γ) : SL(2, ℤ) :=
  ((Quotient.out q : Γ) : SL(2, ℤ))⁻¹

theorem unfoldRep_mem (q : Γ ⧸ Δ.subgroupOf Γ) : unfoldRep Γ Δ q ∈ Γ :=
  Γ.inv_mem (Quotient.out q).2

theorem unfoldRep_cov (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) : ∃ q, γ * (unfoldRep Γ Δ q)⁻¹ ∈ Δ := by
  refine ⟨QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : Γ), ?_⟩
  have h : (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : Γ) : Γ ⧸ Δ.subgroupOf Γ) =
      QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : Γ) : Γ ⧸ Δ.subgroupOf Γ)) :=
    (QuotientGroup.out_eq' _).symm
  rw [QuotientGroup.eq, inv_inv, Subgroup.mem_subgroupOf] at h
  simpa [unfoldRep] using h

theorem unfoldRep_disj (i j : Γ ⧸ Δ.subgroupOf Γ)
    (h : unfoldRep Γ Δ j * (unfoldRep Γ Δ i)⁻¹ ∈ Δ) : i = j := by
  simp only [unfoldRep, inv_inv] at h
  have h' : (Quotient.out j)⁻¹ * Quotient.out i ∈ Δ.subgroupOf Γ := by
    rw [Subgroup.mem_subgroupOf]; exact h
  rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'
  exact h'.symm

end Unfold

section HK1

open ModularForm CongruenceSubgroup
open scoped MatrixGroups

def rmap (p : ℕ) : Option (Fin p) → GL (Fin 2) ℝ
  | some j => heckeMatrix p j
  | none => heckeDiagMatrix p

theorem rmap_uniq {p : ℕ} (hp : 1 < p) (δ : SL(2, ℤ)) {o o' : Option (Fin p)}
    (h : Matrix.SpecialLinearGroup.mapGL ℝ δ * rmap p o = rmap p o') : o = o' := by
  have hp0 : p ≠ 0 := by omega
  match o, o' with
  | some j, some j' =>
      simp only [rmap] at h
      exact congrArg some (Fin.ext (heckeMatrix_coset_inj hp0 j.2 j'.2 δ h))
  | some j, none =>
      simp only [rmap] at h
      exact absurd h (heckeDiagMatrix_ne_mul_heckeMatrix hp j δ)
  | none, some j' =>
      simp only [rmap] at h
      exfalso
      apply heckeDiagMatrix_ne_mul_heckeMatrix hp j' δ⁻¹
      rw [map_inv, ← h]
      group
  | none, none => rfl

variable {p N : ℕ}

theorem exists_decomp (hp : p.Prime) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ o : Option (Fin p),
      heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * rmap p o := by
  obtain ⟨δ, hδ, h | h⟩ := heckeMatrix_mul_mem_coset hp γ hγ
  · obtain ⟨j, hj, hje⟩ := h
    exact ⟨δ, hδ, some ⟨j, hj⟩, hje⟩
  · exact ⟨δ, hδ, none, h⟩

end HK1

section HK1Main

open ModularForm CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

theorem mapGL_eq_toGL_map (γ : SL(2, ℤ)) :
    mapGL ℝ γ = toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ) := rfl

theorem mem_conjGL_mapGL {Γ : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ} {x : SL(2, ℤ)} :
    x ∈ conjGL Γ g ↔ ∃ y ∈ Γ, mapGL ℝ y = g * mapGL ℝ x * g⁻¹ := by
  simp_rw [mem_conjGL, mapGL_eq_toGL_map]

variable {p N : ℕ}

theorem heckeMatrix_mul_unipotent (hp : p ≠ 0) (j : ℕ) (u : SL(2, ℤ))
    (hu : (u : Matrix (Fin 2) (Fin 2) ℤ) = !![(1 : ℤ), (j : ℤ); 0, 1]) :
    heckeMatrix p 0 * mapGL ℝ u = heckeMatrix p j := by
  apply Units.ext
  ext i j₀
  fin_cases i <;> fin_cases j₀ <;>
    simp [Units.val_mul, val_heckeMatrix hp,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, hu,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeT_eq_sum_unfold_of_decomp (hp : p.Prime) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → f ∣[k] mapGL ℝ γ = f)
    (α : GL (Fin 2) ℝ)
    (hdec : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∃ δ, δ ∈ Gamma0 N ∧ ∃ o : Option (Fin p),
      α * mapGL ℝ γ = mapGL ℝ δ * rmap p o)
    (hwit : ∀ o : Option (Fin p), ∃ γo, γo ∈ Gamma0 N ∧ ∃ so, so ∈ Gamma0 N ∧
      α * mapGL ℝ γo = mapGL ℝ so * rmap p o)
    [Fintype ((Gamma0 N : Subgroup SL(2, ℤ)) ⧸
      ((Gamma0 N ⊓ conjGL (Gamma0 N) α).subgroupOf (Gamma0 N)))] :
    ModularForm.heckeT k p f =
      ∑ q : (Gamma0 N : Subgroup SL(2, ℤ)) ⧸
          ((Gamma0 N ⊓ conjGL (Gamma0 N) α).subgroupOf (Gamma0 N)),
        f ∣[k] (α * mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)) := by
  classical
  have hp1 : 1 < p := hp.one_lt
  choose δq hδq oq hoq using fun q : (Gamma0 N : Subgroup SL(2, ℤ)) ⧸
      ((Gamma0 N ⊓ conjGL (Gamma0 N) α).subgroupOf (Gamma0 N)) =>
    hdec _ (unfoldRep_mem (Δ := Gamma0 N ⊓ conjGL (Gamma0 N) α) q)
  have hinj : Function.Injective oq := by
    intro q q' h
    have e1 := hoq q
    have e2 := hoq q'
    rw [h] at e1
    have f1 : mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)
        = α⁻¹ * (mapGL ℝ (δq q) * rmap p (oq q')) := by
      rw [← e1]; group
    have f2 : (mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q'))⁻¹
        = (mapGL ℝ (δq q') * rmap p (oq q'))⁻¹ * α := by
      rw [← e2]; group
    have e3 : mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)
          * (mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q'))⁻¹
        = α⁻¹ * (mapGL ℝ (δq q) * (mapGL ℝ (δq q'))⁻¹) * α := by
      rw [f1, f2]; group
    have hmem : unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q
          * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q')⁻¹
        ∈ Gamma0 N ⊓ conjGL (Gamma0 N) α := by
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (unfoldRep_mem q) (inv_mem (unfoldRep_mem q')), ?_⟩
      refine mem_conjGL_mapGL.mpr ⟨δq q * (δq q')⁻¹, mul_mem (hδq q) (inv_mem (hδq q')), ?_⟩
      rw [map_mul, map_inv, map_mul, map_inv, e3]
      group
    exact (unfoldRep_disj q' q hmem).symm
  have hsurj : Function.Surjective oq := by
    intro o
    obtain ⟨γo, hγo, so, hso, heq⟩ := hwit o
    obtain ⟨q, hq⟩ := unfoldRep_cov (Δ := Gamma0 N ⊓ conjGL (Gamma0 N) α) γo hγo
    have hdΓL : γo * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)⁻¹
        ∈ conjGL (Gamma0 N) α := (Subgroup.mem_inf.mp hq).2
    obtain ⟨y, hyΓ, hy⟩ := mem_conjGL_mapGL.mp hdΓL
    have huR : unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q
        = (γo * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)⁻¹)⁻¹ * γo := by
      group
    have hswap : α * (mapGL ℝ (γo * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)⁻¹))⁻¹
        = (mapGL ℝ y)⁻¹ * α := by
      rw [hy]; group
    have hcomp : α * mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)
        = mapGL ℝ (y⁻¹ * so) * rmap p o := by
      calc α * mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)
          = α * ((mapGL ℝ (γo * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)⁻¹))⁻¹
              * mapGL ℝ γo) := by
            rw [← map_inv, ← map_mul, ← huR]
        _ = (α * (mapGL ℝ (γo * (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)⁻¹))⁻¹)
              * mapGL ℝ γo := by
            group
        _ = (mapGL ℝ y)⁻¹ * (α * mapGL ℝ γo) := by rw [hswap]; group
        _ = (mapGL ℝ y)⁻¹ * (mapGL ℝ so * rmap p o) := by rw [heq]
        _ = mapGL ℝ (y⁻¹ * so) * rmap p o := by rw [map_mul, map_inv]; group
    have hfin : mapGL ℝ ((y⁻¹ * so)⁻¹ * δq q) * rmap p (oq q) = rmap p o := by
      have h5 : mapGL ℝ (δq q) * rmap p (oq q) = mapGL ℝ (y⁻¹ * so) * rmap p o :=
        (hoq q).symm.trans hcomp
      rw [map_mul, map_inv]
      calc (mapGL ℝ (y⁻¹ * so))⁻¹ * mapGL ℝ (δq q) * rmap p (oq q)
          = (mapGL ℝ (y⁻¹ * so))⁻¹ * (mapGL ℝ (δq q) * rmap p (oq q)) := by group
        _ = (mapGL ℝ (y⁻¹ * so))⁻¹ * (mapGL ℝ (y⁻¹ * so) * rmap p o) := by rw [h5]
        _ = rmap p o := by group
    exact ⟨q, rmap_uniq hp1 _ hfin⟩
  calc ModularForm.heckeT k p f
      = ∑ o : Option (Fin p), f ∣[k] rmap p o := by
        rw [Fintype.sum_option, ModularForm.heckeT_def, add_comm]
        congr 1
        simp only [rmap]
        rw [← Fin.sum_univ_eq_sum_range (fun j => f ∣[k] heckeMatrix p j) p]
    _ = ∑ q, f ∣[k] rmap p (oq q) :=
        (Fintype.sum_bijective oq ⟨hinj, hsurj⟩ _ _ (fun q => rfl)).symm
    _ = ∑ q : (Gamma0 N : Subgroup SL(2, ℤ)) ⧸
          ((Gamma0 N ⊓ conjGL (Gamma0 N) α).subgroupOf (Gamma0 N)),
          f ∣[k] (α * mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) α) q)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hoq q, SlashAction.slash_mul, hf _ (hδq q)]

theorem heckeT_eq_sum_unfold (hp : p.Prime) (hpN : ¬ p ∣ N) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → f ∣[k] mapGL ℝ γ = f)
    [Fintype ((Gamma0 N : Subgroup SL(2, ℤ)) ⧸
      ((Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0)).subgroupOf (Gamma0 N)))] :
    ModularForm.heckeT k p f =
      ∑ q : (Gamma0 N : Subgroup SL(2, ℤ)) ⧸
          ((Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0)).subgroupOf (Gamma0 N)),
        f ∣[k] (heckeMatrix p 0 *
          mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0)) q)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  refine heckeT_eq_sum_unfold_of_decomp hp k f hf _ (fun γ hγ => exists_decomp hp hγ) ?_
  intro o
  match o with
  | some j =>
      refine ⟨⟨!![(1 : ℤ), (j : ℤ); 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩,
        ?_, 1, one_mem _, ?_⟩
      · rw [Gamma0_mem]
        show ((0 : ℤ) : ZMod N) = 0
        simp
      · simpa [rmap] using heckeMatrix_mul_unipotent hp0 j
          (⟨!![(1 : ℤ), (j : ℤ); 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩ : SL(2, ℤ)) rfl
  | none =>
      obtain ⟨γ₁, γ₂, h1, h2, h3⟩ := heckeDiagMatrix_eq_mul_heckeMatrix_mul hp0
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
      refine ⟨γ₂, h2, γ₁⁻¹, inv_mem h1, ?_⟩
      show heckeMatrix p 0 * mapGL ℝ γ₂ = mapGL ℝ γ₁⁻¹ * heckeDiagMatrix p
      rw [map_inv, h3]
      group

theorem heckeT_eq_sum_unfold_diag (hp : p.Prime) (hpN : ¬ p ∣ N) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → f ∣[k] mapGL ℝ γ = f)
    [Fintype ((Gamma0 N : Subgroup SL(2, ℤ)) ⧸
      ((Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p)).subgroupOf (Gamma0 N)))] :
    ModularForm.heckeT k p f =
      ∑ q : (Gamma0 N : Subgroup SL(2, ℤ)) ⧸
          ((Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p)).subgroupOf (Gamma0 N)),
        f ∣[k] (heckeDiagMatrix p *
          mapGL ℝ (unfoldRep (Gamma0 N) (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p)) q)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨γ₁, γ₂, h1, h2, h3⟩ := heckeDiagMatrix_eq_mul_heckeMatrix_mul hp0
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
  refine heckeT_eq_sum_unfold_of_decomp hp k f hf _ ?_ ?_
  ·
    intro γ hγ
    obtain ⟨δ, hδ, o, ho⟩ := exists_decomp hp (mul_mem h2 hγ)
    refine ⟨γ₁ * δ, mul_mem h1 hδ, o, ?_⟩
    rw [h3, map_mul]
    calc mapGL ℝ γ₁ * heckeMatrix p 0 * mapGL ℝ γ₂ * mapGL ℝ γ
        = mapGL ℝ γ₁ * (heckeMatrix p 0 * mapGL ℝ (γ₂ * γ)) := by rw [map_mul]; group
      _ = mapGL ℝ γ₁ * (mapGL ℝ δ * rmap p o) := by rw [ho]
      _ = mapGL ℝ γ₁ * mapGL ℝ δ * rmap p o := by group
  ·
    intro o
    match o with
    | some j =>
        have hdetu : Matrix.det !![(1 : ℤ), (j : ℤ); 0, 1] = 1 := by
          rw [Matrix.det_fin_two_of]; ring
        set u : SL(2, ℤ) := ⟨!![(1 : ℤ), (j : ℤ); 0, 1], hdetu⟩ with hu
        have huv : (u : Matrix (Fin 2) (Fin 2) ℤ) = !![(1 : ℤ), (j : ℤ); 0, 1] := by
          rw [hu]
        refine ⟨γ₂⁻¹ * u, mul_mem (inv_mem h2) ?_, γ₁, h1, ?_⟩
        · rw [Gamma0_mem]
          show ((u : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
          rw [huv]
          show ((0 : ℤ) : ZMod N) = 0
          simp
        · have e : heckeDiagMatrix p * mapGL ℝ (γ₂⁻¹ * u)
              = mapGL ℝ γ₁ * (heckeMatrix p 0 * mapGL ℝ u) := by
            rw [h3, map_mul, map_inv]
            group
          rw [e, heckeMatrix_mul_unipotent hp0 j u huv]
          rfl
    | none =>
        exact ⟨1, one_mem _, 1, one_mem _, by simp [rmap]⟩

end HK1Main

section PeterssonAdjoint

open MeasureTheory UpperHalfPlane Complex ModularGroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise Modular ComplexConjugate ModularForm

theorem volume_smul_gl (g : GL (Fin 2) ℝ) (S : Set ℍ) : volume (g • S) = volume S :=
  measure_smul volume g S

theorem setIntegral_gl_smul (g : GL (Fin 2) ℝ) (φ : ℍ → ℂ) (S : Set ℍ) :
    ∫ τ in g • S, φ τ = ∫ τ in S, φ (g • τ) := by
  have h := (measurePreserving_smul g (volume : Measure ℍ)).setIntegral_image_emb
    (measurableEmbedding_const_smul g) φ S
  rw [Set.image_smul] at h
  exact h

theorem sl_smul_eq_mapGL_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    γ • τ = (γ : GL (Fin 2) ℝ) • τ := rfl

theorem sl_smul_set_eq_mapGL_smul (γ : SL(2, ℤ)) (S : Set ℍ) :
    γ • S = (γ : GL (Fin 2) ℝ) • S := rfl

scoped instance : MeasurableConstSMul SL(2, ℤ) ℍ :=
  ⟨fun γ => measurable_const_smul (γ : GL (Fin 2) ℝ)⟩

theorem volume_smul_sl (γ : SL(2, ℤ)) (S : Set ℍ) : volume (γ • S) = volume S := by
  rw [sl_smul_set_eq_mapGL_smul]; exact volume_smul_gl _ S

theorem setIntegral_sl_smul (γ : SL(2, ℤ)) (φ : ℍ → ℂ) (S : Set ℍ) :
    ∫ τ in γ • S, φ τ = ∫ τ in S, φ (γ • τ) := by
  rw [sl_smul_set_eq_mapGL_smul]; exact setIntegral_gl_smul _ φ S

theorem volume_eq_zero_of_image_coe {s : Set ℍ} (hs : volume (UpperHalfPlane.coe '' s) = 0) :
    volume s = 0 := by
  rw [volume_eq_lintegral, setLIntegral_measure_zero _ _ hs]

theorem volume_re_eq_const (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ Set.univ) := by
    ext z; simp [measurableEquivRealProd_apply]
  rw [h, ← Measure.map_apply measurableEquivRealProd.measurable
    ((measurableSet_singleton c).prod MeasurableSet.univ),
    volume_preserving_equiv_real_prod.map_eq, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have h : {z : ℂ | Complex.normSq z = 1} = Metric.sphere (0 : ℂ) 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro hz; nlinarith [norm_nonneg z]
    · intro hz; rw [hz]; norm_num
  rw [h]; exact Measure.addHaar_sphere volume 0 1

theorem volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_image_coe
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪
      ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}))
  · rintro _ ⟨τ, ⟨⟨h1, h2⟩, hno⟩, rfl⟩
    simp only [fdo, Set.mem_setOf_eq, not_and_or, not_lt] at hno
    rcases hno with h | h
    · left; exact le_antisymm h h1
    · right
      have habs : |τ.re| = 1 / 2 := le_antisymm h2 h
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp habs with h' | h'
      · left; exact h'
      · right; exact h'
  · exact measure_union_null volume_normSq_eq_one
      (measure_union_null (volume_re_eq_const _) (volume_re_eq_const _))

theorem measurableSet_fd : MeasurableSet 𝒟 := isClosed_fd.measurableSet

theorem measurableSet_fdo : MeasurableSet 𝒟ᵒ := isOpen_fdo.measurableSet

theorem smul_fdo_inter_fd_eq_empty {g : SL(2, ℤ)} (h1 : g ≠ 1) (h2 : g ≠ -1) :
    (g • 𝒟ᵒ) ∩ 𝒟 = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_smul_set, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨z, hz, rfl⟩ hw
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fd hz hw with h | h
  · exact h1 h
  · exact h2 h

theorem volume_smul_fd_inter_fd {g : SL(2, ℤ)} (h1 : g ≠ 1) (h2 : g ≠ -1) :
    volume ((g • 𝒟) ∩ 𝒟) = 0 := by
  have hsub : (g • 𝒟) ∩ 𝒟 ⊆ g • (𝒟 \ 𝒟ᵒ) := by
    rintro w ⟨⟨z, hz, rfl⟩, hw⟩
    refine ⟨z, ⟨hz, fun hzo => ?_⟩, rfl⟩
    have : g • z ∈ (g • 𝒟ᵒ) ∩ 𝒟 := ⟨Set.smul_mem_smul_set hzo, hw⟩
    rw [smul_fdo_inter_fd_eq_empty h1 h2] at this
    exact this
  exact measure_mono_null hsub (by rw [volume_smul_sl]; exact volume_fd_diff_fdo)

theorem volume_smul_fd_inter_smul_fd {a b : SL(2, ℤ)} (h1 : a ≠ b) (h2 : a ≠ -b) :
    volume ((a • 𝒟) ∩ (b • 𝒟)) = 0 := by
  have hrw : (a • 𝒟) ∩ (b • 𝒟) = b • (((b⁻¹ * a) • 𝒟) ∩ 𝒟) := by
    rw [Set.smul_set_inter, smul_smul, mul_inv_cancel_left]
  rw [hrw, volume_smul_sl]
  refine volume_smul_fd_inter_fd (fun h => h1 ?_) (fun h => h2 ?_)
  · simpa using congrArg (b * ·) h
  · have := congrArg (b * ·) h; simpa using this

theorem mem_center_sl_iff {g : SL(2, ℤ)} :
    g ∈ Subgroup.center SL(2, ℤ) ↔ g = 1 ∨ g = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrA⟩
    rw [Fintype.card_fin] at hr
    rcases sq_eq_one_iff.mp hr with rfl | rfl
    · left; apply Subtype.ext; rw [← hrA]; simp
    · right; apply Subtype.ext; rw [← hrA]; simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

abbrev PSL : Type := SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)

theorem center_le_ker_toPermHom :
    Subgroup.center SL(2, ℤ) ≤ (MulAction.toPermHom SL(2, ℤ) ℍ).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  ext τ : 1
  change g • τ = τ
  rcases mem_center_sl_iff.mp hg with rfl | rfl
  · exact one_smul _ τ
  · have h := SL_neg_smul (1 : SL(2, ℤ)) τ
    rwa [one_smul] at h

def pslPerm : PSL →* Equiv.Perm ℍ :=
  QuotientGroup.lift _ (MulAction.toPermHom SL(2, ℤ) ℍ) center_le_ker_toPermHom

scoped instance : MulAction PSL ℍ := MulAction.compHom ℍ pslPerm

@[scoped simp] theorem psl_mk_smul (g : SL(2, ℤ)) (τ : ℍ) :
    (QuotientGroup.mk g : PSL) • τ = g • τ := rfl

theorem psl_mk_smul_set (g : SL(2, ℤ)) (S : Set ℍ) :
    (QuotientGroup.mk g : PSL) • S = g • S := by
  ext z; simp only [Set.mem_smul_set, psl_mk_smul]

theorem psl_mk_eq_one_iff {g : SL(2, ℤ)} :
    (QuotientGroup.mk g : PSL) = 1 ↔ g = 1 ∨ g = -1 := by
  rw [QuotientGroup.eq_one_iff, mem_center_sl_iff]

theorem psl_mk_eq_mk_iff {a b : SL(2, ℤ)} :
    (QuotientGroup.mk a : PSL) = QuotientGroup.mk b ↔ a = b ∨ a = -b := by
  rw [QuotientGroup.eq, mem_center_sl_iff]
  constructor
  · rintro (h | h)
    · left; exact inv_mul_eq_one.mp h
    · right; rw [inv_mul_eq_iff_eq_mul] at h; rw [h, mul_neg_one, neg_neg]
  · rintro (rfl | rfl)
    · left; simp
    · right; simp

scoped instance : Countable SL(2, ℤ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact Subtype.countable

scoped instance : Countable PSL := inferInstanceAs (Countable (Quotient _))

scoped instance : MeasurableSpace PSL := ⊤

scoped instance : MeasurableSingletonClass PSL := ⟨fun _ => trivial⟩

scoped instance : MeasurableSMul PSL ℍ where
  measurable_const_smul gb := by
    induction gb using QuotientGroup.induction_on with | H γ =>
    change Measurable fun τ : ℍ => γ • τ
    exact measurable_const_smul γ
  measurable_smul_const _ := measurable_of_countable _

scoped instance : SMulInvariantMeasure PSL ℍ (volume : Measure ℍ) where
  measure_preimage_smul gb s _ := by
    induction gb using QuotientGroup.induction_on with | H γ =>
    change volume ((fun τ : ℍ => γ • τ) ⁻¹' s) = volume s
    rw [Set.preimage_smul, volume_smul_sl]

abbrev PΓ (Γ : Subgroup SL(2, ℤ)) : Subgroup PSL := Γ.map (QuotientGroup.mk' _)

scoped instance (S : Subgroup PSL) : MeasurableSMul S ℍ where
  measurable_const_smul c := measurable_const_smul (c : PSL)
  measurable_smul_const _ := measurable_of_countable _

scoped instance (S : Subgroup PSL) : SMulInvariantMeasure S ℍ (volume : Measure ℍ) :=
  ⟨fun c _ hs => SMulInvariantMeasure.measure_preimage_smul (c : PSL) hs⟩

def PΓ.mk {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) : PΓ Γ :=
  ⟨QuotientGroup.mk γ, Subgroup.mem_map_of_mem _ hγ⟩

@[scoped simp] theorem PΓ.mk_smul {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    PΓ.mk γ hγ • τ = γ • τ := rfl

p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"
theorem PΓ.mk_smul_set {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (S : Set ℍ) :
    PΓ.mk γ hγ • S = γ • S := by
  ext z; simp only [Set.mem_smul_set, PΓ.mk_smul]

theorem PΓ.exists_eq_mk {Γ : Subgroup SL(2, ℤ)} (g : PΓ Γ) :
    ∃ (γ : SL(2, ℤ)) (hγ : γ ∈ Γ), g = PΓ.mk γ hγ := by
  obtain ⟨γ, hγ, hg⟩ := Subgroup.mem_map.mp g.2
  exact ⟨γ, hγ, Subtype.ext hg.symm⟩

theorem PΓ.mk_eq_one_iff {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    PΓ.mk γ hγ = 1 ↔ γ = 1 ∨ γ = -1 := by
  rw [PΓ.mk, Subgroup.mk_eq_one, psl_mk_eq_one_iff]

theorem isFundamentalDomain_fd :
    IsFundamentalDomain (PΓ ⊤) 𝒟 (volume : Measure ℍ) where
  nullMeasurableSet := measurableSet_fd.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun z => by
    obtain ⟨g, hg⟩ := exists_smul_mem_fd z
    exact ⟨PΓ.mk g trivial, hg⟩
  aedisjoint := fun a b hne => by
    obtain ⟨γ, hγ, rfl⟩ := PΓ.exists_eq_mk a
    obtain ⟨δ, hδ, rfl⟩ := PΓ.exists_eq_mk b
    change volume (PΓ.mk γ hγ • 𝒟 ∩ PΓ.mk δ hδ • 𝒟) = 0
    rw [PΓ.mk_smul_set, PΓ.mk_smul_set]
    refine volume_smul_fd_inter_smul_fd (fun h => hne ?_) (fun h => hne ?_)
    · subst h; rfl
    · subst h; apply Subtype.ext; change (QuotientGroup.mk (-δ) : PSL) = QuotientGroup.mk δ
      rw [psl_mk_eq_mk_iff]; right; rfl

section Tiling

variable {Γ Δ : Subgroup SL(2, ℤ)} {ι : Type*} {s : Set ℍ} {b : ι → SL(2, ℤ)}

theorem isFundamentalDomain_iUnion_smul [Countable ι] (hΔΓ : Δ ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Δ)
    (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ))
    (hb : ∀ i, b i ∈ Γ) (hcov : ∀ γ ∈ Γ, ∃ i, γ * (b i)⁻¹ ∈ Δ)
    (hdisj : ∀ i j, b j * (b i)⁻¹ ∈ Δ → i = j) :
    IsFundamentalDomain (PΓ Δ) (⋃ i, b i • s) (volume : Measure ℍ) where
  nullMeasurableSet := .iUnion fun i => by
    rw [← PΓ.mk_smul_set (b i) (hb i)]; exact hs.nullMeasurableSet.smul _
  ae_covers := by
    filter_upwards [hs.ae_covers] with z hz
    obtain ⟨g, hg⟩ := hz
    obtain ⟨γ, hγ, rfl⟩ := PΓ.exists_eq_mk g
    rw [PΓ.mk_smul] at hg
    obtain ⟨i, hi⟩ := hcov γ⁻¹ (Γ.inv_mem hγ)
    have hδ : b i * γ ∈ Δ := by
      have := Δ.inv_mem hi; rwa [mul_inv_rev, inv_inv, inv_inv] at this
    refine ⟨PΓ.mk (b i * γ) hδ, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    rw [PΓ.mk_smul, Set.mem_smul_set_iff_inv_smul_mem, smul_smul, inv_mul_cancel_left]
    exact hg
  aedisjoint := fun g g' hne => by
    obtain ⟨ε, hε, rfl⟩ := PΓ.exists_eq_mk g
    obtain ⟨ε', hε', rfl⟩ := PΓ.exists_eq_mk g'
    change volume (PΓ.mk ε hε • (⋃ i, b i • s) ∩ PΓ.mk ε' hε' • (⋃ i, b i • s)) = 0
    rw [PΓ.mk_smul_set, PΓ.mk_smul_set, Set.smul_set_iUnion, Set.smul_set_iUnion,
      Set.iUnion_inter]
    refine measure_iUnion_null fun i => ?_
    rw [Set.inter_iUnion]
    refine measure_iUnion_null fun j => ?_
    rw [smul_smul, smul_smul]

    have hi : ε * b i ∈ Γ := Γ.mul_mem (hΔΓ hε) (hb i)
    have hj : ε' * b j ∈ Γ := Γ.mul_mem (hΔΓ hε') (hb j)
    rw [← PΓ.mk_smul_set _ hi, ← PΓ.mk_smul_set _ hj]
    refine hs.aedisjoint fun heq => hne ?_

    have heq' : (QuotientGroup.mk (ε * b i) : PSL) = QuotientGroup.mk (ε' * b j) :=
      congrArg Subtype.val heq
    rw [psl_mk_eq_mk_iff] at heq'
    have hmem : b j * (b i)⁻¹ ∈ Δ := by
      rcases heq' with h | h
      · have : b j * (b i)⁻¹ = ε'⁻¹ * ε := calc
          b j * (b i)⁻¹ = ε'⁻¹ * (ε' * b j) * (b i)⁻¹ := by rw [inv_mul_cancel_left]
          _ = ε'⁻¹ * (ε * b i) * (b i)⁻¹ := by rw [← h]
          _ = ε'⁻¹ * ε := by rw [mul_assoc, mul_inv_cancel_right]
        rw [this]; exact Δ.mul_mem (Δ.inv_mem hε') hε
      · have h' : ε' * b j = -(ε * b i) := (neg_eq_iff_eq_neg.mpr h).symm
        have : b j * (b i)⁻¹ = -(ε'⁻¹ * ε) := calc
          b j * (b i)⁻¹ = ε'⁻¹ * (ε' * b j) * (b i)⁻¹ := by rw [inv_mul_cancel_left]
          _ = ε'⁻¹ * (-(ε * b i)) * (b i)⁻¹ := by rw [h']
          _ = -(ε'⁻¹ * ε) := by rw [mul_neg, neg_mul, mul_assoc, mul_inv_cancel_right]
        rw [this, neg_eq_neg_one_mul]
        exact Δ.mul_mem hneg (Δ.mul_mem (Δ.inv_mem hε') hε)
    obtain rfl := hdisj i j hmem
    apply Subtype.ext
    change (QuotientGroup.mk ε : PSL) = QuotientGroup.mk ε'
    rw [psl_mk_eq_mk_iff]
    rcases heq' with h | h
    · left; exact mul_right_cancel h
    · right; rw [← neg_mul] at h; exact mul_right_cancel h

theorem volume_smul_inter_smul_eq_zero (hneg : (-1 : SL(2, ℤ)) ∈ Δ)
    (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ))
    (hb : ∀ i, b i ∈ Γ) (hdisj : ∀ i j, b j * (b i)⁻¹ ∈ Δ → i = j) {i j : ι} (hij : i ≠ j) :
    volume (b i • s ∩ b j • s) = 0 := by
  rw [← PΓ.mk_smul_set _ (hb i), ← PΓ.mk_smul_set _ (hb j)]
  refine hs.aedisjoint fun heq => hij ?_
  have heq' : (QuotientGroup.mk (b i) : PSL) = QuotientGroup.mk (b j) := congrArg Subtype.val heq
  rw [psl_mk_eq_mk_iff] at heq'
  refine hdisj i j ?_
  rcases heq' with h | h
  · rw [← h, mul_inv_cancel]; exact Δ.one_mem
  · have hj : b j = -b i := by rw [h, neg_neg]
    rw [hj, neg_mul, mul_inv_cancel]; exact hneg

theorem setIntegral_iUnion_smul [Fintype ι] (hneg : (-1 : SL(2, ℤ)) ∈ Δ)
    (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ)) (hsm : MeasurableSet s)
    (hb : ∀ i, b i ∈ Γ) (hdisj : ∀ i j, b j * (b i)⁻¹ ∈ Δ → i = j)
    (φ : ℍ → ℂ) (hφ : ∀ i, IntegrableOn φ (b i • s)) :
    ∫ τ in ⋃ i, b i • s, φ τ = ∑ i, ∫ τ in s, φ (b i • τ) := by
  rw [integral_iUnion_ae (fun i => (hsm.const_smul (b i)).nullMeasurableSet)
    (fun i j hij => volume_smul_inter_smul_eq_zero hneg hs hb hdisj hij)
    (integrableOn_finite_iUnion.mpr hφ), tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => setIntegral_sl_smul (b i) φ s

end Tiling
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

def gammaFD' (Δ : Subgroup SL(2, ℤ)) : Set ℍ := ⋃ q : SL(2, ℤ) ⧸ Δ, (Quotient.out q)⁻¹ • 𝒟

scoped instance (Δ : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ Δ) :=
  inferInstanceAs (Countable (Quotient _))

scoped instance (Γ : Subgroup SL(2, ℤ)) (H : Subgroup Γ) : Countable (Γ ⧸ H) :=
  inferInstanceAs (Countable (Quotient _))

theorem isFundamentalDomain_gammaFD' (Δ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Δ) :
    IsFundamentalDomain (PΓ Δ) (gammaFD' Δ) (volume : Measure ℍ) := by
  refine isFundamentalDomain_iUnion_smul (Γ := ⊤) le_top hneg isFundamentalDomain_fd
    (fun _ => trivial) (fun γ _ => ?_) (fun i j hij => ?_)
  · have h : (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Δ) =
        QuotientGroup.mk (Quotient.out (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Δ)) :=
      (QuotientGroup.out_eq' _).symm
    rw [QuotientGroup.eq, inv_inv] at h
    exact ⟨_, by rwa [inv_inv]⟩
  · rw [inv_inv, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq'] at hij
    exact hij.symm

theorem measurableSet_gammaFD' (Δ : Subgroup SL(2, ℤ)) : MeasurableSet (gammaFD' Δ) :=
  .iUnion fun _ => measurableSet_fd.const_smul _

section Unfold

variable {Γ Δ : Subgroup SL(2, ℤ)}

theorem isFundamentalDomain_unfold (hΔΓ : Δ ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∈ Δ) {s : Set ℍ}
    (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ)) :
    IsFundamentalDomain (PΓ Δ) (⋃ q, unfoldRep Γ Δ q • s) (volume : Measure ℍ) :=
  isFundamentalDomain_iUnion_smul hΔΓ hneg hs unfoldRep_mem unfoldRep_cov unfoldRep_disj

theorem setIntegral_unfold [Fintype (Γ ⧸ Δ.subgroupOf Γ)] (hneg : (-1 : SL(2, ℤ)) ∈ Δ)
    {s : Set ℍ} (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ)) (hsm : MeasurableSet s)
    (φ : ℍ → ℂ) (hφ : ∀ q, IntegrableOn φ (unfoldRep Γ Δ q • s)) :
    ∫ τ in ⋃ q, unfoldRep Γ Δ q • s, φ τ = ∑ q, ∫ τ in s, φ (unfoldRep Γ Δ q • τ) :=
  setIntegral_iUnion_smul hneg hs hsm unfoldRep_mem unfoldRep_disj φ hφ

theorem measurableSet_unfold {s : Set ℍ} (hsm : MeasurableSet s) :
    MeasurableSet (⋃ q, unfoldRep Γ Δ q • s) :=
  .iUnion fun _ => hsm.const_smul _

theorem volume_unfold_lt_top [Fintype (Γ ⧸ Δ.subgroupOf Γ)] {s : Set ℍ} (hvol : volume s < ⊤) :
    volume (⋃ q, unfoldRep Γ Δ q • s) < ⊤ := by
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype, ENNReal.sum_lt_top]
  intro q _
  rw [volume_smul_sl]; exact hvol

end Unfold
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section Conj

open CongruenceSubgroup

theorem mapGL_inj {x y : SL(2, ℤ)} : (x : GL (Fin 2) ℝ) = (y : GL (Fin 2) ℝ) ↔ x = y := by
  constructor
  · intro h
    apply Subtype.ext
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
    simpa using this
  · rintro rfl; rfl

theorem mapGL_neg (x : SL(2, ℤ)) : ((-x : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(x : GL (Fin 2) ℝ) := by
  ext i j
  simp

variable {Δ Δ' : Subgroup SL(2, ℤ)} (α : GL (Fin 2) ℝ)

theorem isFundamentalDomain_smul_of_le_conjGL (h₁ : Δ ≤ conjGL Δ' α) (h₂ : Δ' ≤ conjGL Δ α⁻¹)
    {s : Set ℍ} (hs : IsFundamentalDomain (PΓ Δ) s (volume : Measure ℍ)) :
    IsFundamentalDomain (PΓ Δ') (α • s) (volume : Measure ℍ) where
  nullMeasurableSet := hs.nullMeasurableSet.smul α
  ae_covers := by
    have hae := (measurePreserving_smul α⁻¹ (volume : Measure ℍ)).quasiMeasurePreserving.ae
      hs.ae_covers
    filter_upwards [hae] with z hz
    obtain ⟨g, hg⟩ := hz
    obtain ⟨x, hx, rfl⟩ := PΓ.exists_eq_mk g
    obtain ⟨y, hy, hyeq⟩ := mem_conjGL.mp (h₁ hx)
    refine ⟨PΓ.mk y hy, ?_⟩
    rw [PΓ.mk_smul, Set.mem_smul_set_iff_inv_smul_mem, sl_smul_eq_mapGL_smul, smul_smul, hyeq,
      ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, ← smul_smul]
    rw [PΓ.mk_smul] at hg
    exact hg
  aedisjoint := fun g g' hne => by
    obtain ⟨y, hy, rfl⟩ := PΓ.exists_eq_mk g
    obtain ⟨y', hy', rfl⟩ := PΓ.exists_eq_mk g'
    obtain ⟨x, hx, hxeq⟩ := mem_conjGL.mp (h₂ hy)
    obtain ⟨x', hx', hx'eq⟩ := mem_conjGL.mp (h₂ hy')
    rw [inv_inv] at hxeq hx'eq

    have key : ∀ {y x : SL(2, ℤ)} (hy : y ∈ Δ'),
        (x : GL (Fin 2) ℝ) = α⁻¹ * (y : GL (Fin 2) ℝ) * α →
        PΓ.mk y hy • (α • s) = α • (x • s) := by
      intro y x hy hxy
      rw [PΓ.mk_smul_set, sl_smul_set_eq_mapGL_smul, sl_smul_set_eq_mapGL_smul, smul_smul,
        smul_smul, hxy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    change volume (PΓ.mk y hy • (α • s) ∩ PΓ.mk y' hy' • (α • s)) = 0
    rw [key hy hxeq, key hy' hx'eq, ← Set.smul_set_inter, volume_smul_gl,
      ← PΓ.mk_smul_set x hx, ← PΓ.mk_smul_set x' hx']
    refine hs.aedisjoint fun heq => hne ?_
    have heq' : (QuotientGroup.mk x : PSL) = QuotientGroup.mk x' := congrArg Subtype.val heq
    apply Subtype.ext
    change (QuotientGroup.mk y : PSL) = QuotientGroup.mk y'
    rw [psl_mk_eq_mk_iff] at heq' ⊢
    have hyx : ∀ {y x : SL(2, ℤ)}, (x : GL (Fin 2) ℝ) = α⁻¹ * (y : GL (Fin 2) ℝ) * α →
        (y : GL (Fin 2) ℝ) = α * (x : GL (Fin 2) ℝ) * α⁻¹ := by
      intro y x hxy
      rw [hxy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]
    rcases heq' with h | h
    · left; rw [← mapGL_inj, hyx hxeq, hyx hx'eq, h]
    · right
      rw [← mapGL_inj, mapGL_neg, hyx hxeq, hyx hx'eq, h, mapGL_neg]
      simp only [mul_neg, neg_mul]

end Conj
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section Kernel

open ModularForm

theorem gl_smul_eq_of_coe_eq_smul {g g' : GL (Fin 2) ℝ} {c : ℝ} (hc : 0 < c)
    (h : (g' : Matrix (Fin 2) (Fin 2) ℝ) = c • (g : Matrix (Fin 2) (Fin 2) ℝ))
    (hg : 0 < g.det.val) (τ : ℍ) : g' • τ = g • τ := by
  have he : ∀ i j, g' i j = c * g i j := fun i j => by
    rw [h]; rfl
  have hdet : g'.det.val = c ^ 2 * g.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, h,
      Matrix.det_smul, Fintype.card_fin]
  have hg' : 0 < g'.det.val := by rw [hdet]; positivity
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hg', coe_smul_of_det_pos hg]
  simp only [num, denom, he]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hden : (↑(g 1 0) : ℂ) * (τ : ℂ) + ↑(g 1 1) ≠ 0 := denom_ne_zero g τ
  push_cast
  field_simp

theorem slash_eq_of_coe_eq_smul (k : ℤ) (f : ℍ → ℂ) {g g' : GL (Fin 2) ℝ} {c : ℝ} (hc : 0 < c)
    (h : (g' : Matrix (Fin 2) (Fin 2) ℝ) = c • (g : Matrix (Fin 2) (Fin 2) ℝ))
    (hg : 0 < g.det.val) : f ∣[k] g' = ((c : ℂ) ^ (k - 2)) • f ∣[k] g := by
  have he : ∀ i j, g' i j = c * g i j := fun i j => by
    rw [h]; rfl
  have hdet : g'.det.val = c ^ 2 * g.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, h,
      Matrix.det_smul, Fintype.card_fin]
  have hg' : 0 < g'.det.val := by rw [hdet]; positivity
  have hσ : σ g' = σ g := by
    unfold σ; rw [if_pos hg', if_pos hg]
  ext τ
  rw [slash_apply, Pi.smul_apply, slash_apply, smul_eq_mul, hσ, gl_smul_eq_of_coe_eq_smul hc h hg,
    hdet]
  have hdenom : denom g' τ = (c : ℂ) * denom g τ := by
    simp only [denom, he]; push_cast; ring
  rw [hdenom, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set D : ℝ := |g.det.val|
  push_cast

  have key : ((c : ℂ) ^ 2) ^ (k - 1) * (c : ℂ) ^ (-k) = (c : ℂ) ^ (k - 2) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hc']; congr 1; push_cast; ring
  rw [mul_zpow, mul_zpow, ← key]
  ring

theorem petersson_slash_left (k : ℤ) (f g : ℍ → ℂ) {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (τ : ℍ) :
    petersson k (f ∣[k] α) g τ =
      ((α.det.val : ℂ) ^ (k - 2)) * petersson k f (g ∣[k] α⁻¹) (α • τ) := by
  have h := petersson_slash k f (g ∣[k] α⁻¹) α τ
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one, abs_of_pos hα] at h
  rw [h]
  unfold σ; rw [if_pos hα]; rfl

theorem continuous_slash (k : ℤ) {f : ℍ → ℂ} (hf : Continuous f) (g : GL (Fin 2) ℝ) :
    Continuous (f ∣[k] g) := by
  rw [slash_def]
  refine ((σ g).continuous.comp (hf.comp (continuous_const_smul g))).mul continuous_const |>.mul ?_
  refine Continuous.zpow₀ ?_ (-k) fun τ => Or.inl (denom_ne_zero g τ)
  unfold denom; fun_prop

theorem petersson_add_left (k : ℤ) (f₁ f₂ g : ℍ → ℂ) (τ : ℍ) :
    petersson k (f₁ + f₂) g τ = petersson k f₁ g τ + petersson k f₂ g τ := by
  simp only [petersson, Pi.add_apply, map_add]; ring

theorem petersson_add_right (k : ℤ) (f g₁ g₂ : ℍ → ℂ) (τ : ℍ) :
    petersson k f (g₁ + g₂) τ = petersson k f g₁ τ + petersson k f g₂ τ := by
  simp only [petersson, Pi.add_apply]; ring

theorem petersson_zero_left (k : ℤ) (g : ℍ → ℂ) (τ : ℍ) : petersson k 0 g τ = 0 := by
  simp [petersson]

theorem petersson_zero_right (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) : petersson k f 0 τ = 0 := by
  simp [petersson]

theorem petersson_sum_left (k : ℤ) {ι : Type*} (t : Finset ι) (f : ι → ℍ → ℂ) (g : ℍ → ℂ)
    (τ : ℍ) : petersson k (∑ i ∈ t, f i) g τ = ∑ i ∈ t, petersson k (f i) g τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [petersson_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, petersson_add_left, ih]

theorem petersson_sum_right (k : ℤ) {ι : Type*} (t : Finset ι) (f : ℍ → ℂ) (g : ι → ℍ → ℂ)
    (τ : ℍ) : petersson k f (∑ i ∈ t, g i) τ = ∑ i ∈ t, petersson k f (g i) τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [petersson_zero_right]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, petersson_add_right, ih]

theorem petersson_smul_right (k : ℤ) (f g : ℍ → ℂ) (a : ℂ) (τ : ℍ) :
    petersson k f (a • g) τ = a * petersson k f g τ := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem petersson_sl_smul (k : ℤ) (f g : ℍ → ℂ) (δ : SL(2, ℤ)) (τ : ℍ) :
    petersson k f g (δ • τ) = petersson k (f ∣[k] (δ : GL (Fin 2) ℝ)) (g ∣[k] (δ : GL (Fin 2) ℝ)) τ :=
  (petersson_slash_SL k f g δ τ).symm

theorem petersson_bounded_of_cuspForm (k : ℤ) {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
    [Γ₁.IsArithmetic] [Γ₂.IsArithmetic] {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [CuspFormClass F₁ Γ₁ k] [CuspFormClass F₂ Γ₂ k] (f : F₁) (g : F₂) :
    ∃ C, ∀ τ, ‖petersson k f g τ‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := CuspFormClass.exists_bound (Γ := Γ₁) (k := k) f
  obtain ⟨C₂, hC₂⟩ := CuspFormClass.exists_bound (Γ := Γ₂) (k := k) g
  refine ⟨C₁ * C₂, fun τ => ?_⟩
  have hy : 0 < τ.im := τ.im_pos
  have hyk : 0 < τ.im ^ (k / 2 : ℝ) := Real.rpow_pos_of_pos hy _
  have h1 := hC₁ τ
  have h2 := hC₂ τ
  have hC₁' : 0 ≤ C₁ := by
    have := (norm_nonneg _).trans h1
    exact le_of_mul_le_mul_right (by simpa [div_eq_mul_inv] using this : 0 * (τ.im ^ (k / 2 : ℝ))⁻¹
      ≤ C₁ * (τ.im ^ (k / 2 : ℝ))⁻¹) (inv_pos.mpr hyk)
  have hnorm : ‖petersson k f g τ‖ = ‖f τ‖ * ‖g τ‖ * τ.im ^ (k / 2 : ℝ) * τ.im ^ (k / 2 : ℝ) := by
    rw [petersson, norm_mul, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy, mul_assoc (‖f τ‖ * ‖g τ‖), ← Real.rpow_add hy,
      add_halves, Real.rpow_intCast]
  rw [hnorm]
  calc ‖f τ‖ * ‖g τ‖ * τ.im ^ (k / 2 : ℝ) * τ.im ^ (k / 2 : ℝ)
      = (‖f τ‖ * τ.im ^ (k / 2 : ℝ)) * (‖g τ‖ * τ.im ^ (k / 2 : ℝ)) := by ring
    _ ≤ C₁ * C₂ := by
        apply mul_le_mul
        · exact (le_div_iff₀ hyk).mp h1
        · exact (le_div_iff₀ hyk).mp h2
        · positivity
        · exact hC₁'

theorem integrableOn_of_bounded_continuous {φ : ℍ → ℂ} (hφ : Continuous φ)
    (hb : ∃ C, ∀ τ, ‖φ τ‖ ≤ C) {S : Set ℍ} (hS : volume S < ⊤) : IntegrableOn φ S := by
  obtain ⟨C, hC⟩ := hb
  exact IntegrableOn.of_bound hS hφ.aestronglyMeasurable.restrict C (ae_of_all _ hC)

end Kernel
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section Assembly

open CongruenceSubgroup

theorem conj_eq_of_coe_eq_smul {β γ : GL (Fin 2) ℝ} {d : ℝ}
    (h : (β : Matrix (Fin 2) (Fin 2) ℝ) = d • (γ : Matrix (Fin 2) (Fin 2) ℝ)) (y : GL (Fin 2) ℝ) :
    β * y * β⁻¹ = γ * y * γ⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul]
  rw [h, Matrix.smul_mul, Matrix.mul_smul, mul_assoc ((γ : Matrix (Fin 2) (Fin 2) ℝ) * y),
    Units.inv_mul, mul_one]

theorem conjGL_eq_of_coe_eq_smul (Γ : Subgroup SL(2, ℤ)) {β γ : GL (Fin 2) ℝ} {d : ℝ}
    (h : (β : Matrix (Fin 2) (Fin 2) ℝ) = d • (γ : Matrix (Fin 2) (Fin 2) ℝ)) :
    conjGL Γ β = conjGL Γ γ := by
  ext x
  simp only [mem_conjGL, conj_eq_of_coe_eq_smul h]

variable {Γ : Subgroup SL(2, ℤ)} {α : GL (Fin 2) ℝ}

theorem le_conjGL_inf (Γ : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) :
    Γ ⊓ conjGL Γ α ≤ conjGL (Γ ⊓ conjGL Γ α⁻¹) α := by
  rintro x ⟨hx, hx'⟩
  obtain ⟨y, hy, hyeq⟩ := mem_conjGL.mp hx'
  refine mem_conjGL.mpr ⟨y, ⟨hy, mem_conjGL.mpr ⟨x, hx, ?_⟩⟩, hyeq⟩
  rw [hyeq, inv_inv]; group

theorem le_conjGL_inf' (Γ : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) :
    Γ ⊓ conjGL Γ α⁻¹ ≤ conjGL (Γ ⊓ conjGL Γ α) α⁻¹ := by
  have h := le_conjGL_inf Γ α⁻¹
  rwa [inv_inv] at h

theorem neg_one_mem_inf_conjGL (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (α : GL (Fin 2) ℝ) :
    (-1 : SL(2, ℤ)) ∈ Γ ⊓ conjGL Γ α := by
  refine ⟨hneg, mem_conjGL.mpr ⟨-1, hneg, ?_⟩⟩
  rw [mapGL_neg]; simp

theorem petersson_slash_right_invariant (k : ℤ) {f g : ℍ → ℂ} (β : GL (Fin 2) ℝ)
    (hf : ∀ γ ∈ Γ, f ∣[k] (γ : GL (Fin 2) ℝ) = f) (hg : ∀ γ ∈ Γ, g ∣[k] (γ : GL (Fin 2) ℝ) = g)
    {y : SL(2, ℤ)} (hy : y ∈ Γ ⊓ conjGL Γ β) (τ : ℍ) :
    petersson k f (g ∣[k] β) (y • τ) = petersson k f (g ∣[k] β) τ := by
  obtain ⟨hyΓ, hy'⟩ := hy
  obtain ⟨z, hz, hzeq⟩ := mem_conjGL.mp hy'
  have hβy : β * (y : GL (Fin 2) ℝ) = (z : GL (Fin 2) ℝ) * β := by
    rw [hzeq, inv_mul_cancel_right]
  rw [petersson_sl_smul, hf y hyΓ, ← SlashAction.slash_mul, hβy, SlashAction.slash_mul, hg z hz]

theorem setIntegral_petersson_doubleCoset_symm (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hα : 0 < α.det.val) {α' : GL (Fin 2) ℝ}
    (hα' : (α' : Matrix (Fin 2) (Fin 2) ℝ) = α.det.val • ((α⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    {Δ Δ' : Subgroup SL(2, ℤ)} (hΔ : Δ = Γ ⊓ conjGL Γ α) (hΔ' : Δ' = Γ ⊓ conjGL Γ α')
    [Fintype (Γ ⧸ Δ.subgroupOf Γ)] [Fintype (Γ ⧸ Δ'.subgroupOf Γ)]
    {s : Set ℍ} (hsm : MeasurableSet s) (hvol : volume s < ⊤)
    (hs : IsFundamentalDomain (PΓ Γ) s (volume : Measure ℍ))
    (k : ℤ) {f g : ℍ → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ γ ∈ Γ, f ∣[k] (γ : GL (Fin 2) ℝ) = f) (hg : ∀ γ ∈ Γ, g ∣[k] (γ : GL (Fin 2) ℝ) = g)
    (hφ : ∃ C, ∀ τ, ‖petersson k (f ∣[k] α) g τ‖ ≤ C)
    (hψ : ∃ C, ∀ τ, ‖petersson k f (g ∣[k] α') τ‖ ≤ C) :
    ∫ τ in s, petersson k (∑ q, f ∣[k] (α * (unfoldRep Γ Δ q : GL (Fin 2) ℝ))) g τ
      = ∫ τ in s, petersson k f (∑ q, g ∣[k] (α' * (unfoldRep Γ Δ' q : GL (Fin 2) ℝ))) τ := by
  set φ : ℍ → ℂ := petersson k (f ∣[k] α) g with hφdef
  set ψ : ℍ → ℂ := petersson k f (g ∣[k] α') with hψdef
  have hαinv : 0 < (α⁻¹ : GL (Fin 2) ℝ).det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.mpr hα
  have hΔ'eq : conjGL Γ α' = conjGL Γ α⁻¹ := conjGL_eq_of_coe_eq_smul Γ hα'
  have hφc : Continuous φ := petersson_continuous k (continuous_slash k hfc α) hgc
  have hψc : Continuous ψ := petersson_continuous k hfc (continuous_slash k hgc α')
  have hbdd_comp : ∀ {χ : ℍ → ℂ} (δ : SL(2, ℤ)), (∃ C, ∀ τ, ‖χ τ‖ ≤ C) →
      ∃ C, ∀ τ, ‖χ (δ • τ)‖ ≤ C := fun δ ⟨C, hC⟩ => ⟨C, fun τ => hC _⟩

  set s₁ : Set ℍ := ⋃ q, unfoldRep Γ Δ q • s with hs₁def
  set s₂ : Set ℍ := ⋃ q, unfoldRep Γ Δ' q • s with hs₂def
  have hΔneg : (-1 : SL(2, ℤ)) ∈ Δ := hΔ ▸ neg_one_mem_inf_conjGL hneg α
  have hΔ'neg : (-1 : SL(2, ℤ)) ∈ Δ' := hΔ' ▸ neg_one_mem_inf_conjGL hneg α'
  have hs₁ : IsFundamentalDomain (PΓ Δ) s₁ (volume : Measure ℍ) :=
    isFundamentalDomain_unfold (hΔ ▸ inf_le_left) hΔneg hs
  have hs₂ : IsFundamentalDomain (PΓ Δ') s₂ (volume : Measure ℍ) :=
    isFundamentalDomain_unfold (hΔ' ▸ inf_le_left) hΔ'neg hs
  have hαs₁ : IsFundamentalDomain (PΓ Δ') (α • s₁) (volume : Measure ℍ) := by
    refine isFundamentalDomain_smul_of_le_conjGL α ?_ ?_ hs₁
    · rw [hΔ, hΔ', hΔ'eq]; exact le_conjGL_inf Γ α
    · rw [hΔ, hΔ', hΔ'eq]; exact le_conjGL_inf' Γ α

  have hker : ∀ τ, φ τ = ψ (α • τ) := fun τ => by
    rw [hφdef, hψdef, petersson_slash_left k f g hα, slash_eq_of_coe_eq_smul k g hα hα' hαinv,
      petersson_smul_right]

  have hψinv : ∀ (y : PΓ Δ') (τ : ℍ), ψ (y • τ) = ψ τ := fun y τ => by
    obtain ⟨y, hy, rfl⟩ := PΓ.exists_eq_mk y
    rw [PΓ.mk_smul]
    exact petersson_slash_right_invariant k α' hf hg (hΔ' ▸ hy) τ
  calc ∫ τ in s, petersson k (∑ q, f ∣[k] (α * (unfoldRep Γ Δ q : GL (Fin 2) ℝ))) g τ
      = ∫ τ in s, ∑ q, φ (unfoldRep Γ Δ q • τ) := by
        refine setIntegral_congr_fun hsm fun τ _ => ?_
        rw [petersson_sum_left]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hφdef, petersson_sl_smul, ← SlashAction.slash_mul, hg _ (unfoldRep_mem q)]
    _ = ∑ q, ∫ τ in s, φ (unfoldRep Γ Δ q • τ) :=
        integral_finsetSum _ fun q _ => integrableOn_of_bounded_continuous
          (hφc.comp (continuous_const_smul (unfoldRep Γ Δ q : GL (Fin 2) ℝ))) (hbdd_comp _ hφ) hvol
    _ = ∫ τ in s₁, φ τ := (setIntegral_unfold hΔneg hs hsm φ fun q =>
          integrableOn_of_bounded_continuous hφc hφ (by rw [volume_smul_sl]; exact hvol)).symm
    _ = ∫ τ in s₁, ψ (α • τ) := by simp_rw [hker]
    _ = ∫ τ in α • s₁, ψ τ := (setIntegral_gl_smul α ψ s₁).symm
    _ = ∫ τ in s₂, ψ τ := hαs₁.setIntegral_eq hs₂ hψinv
    _ = ∑ q, ∫ τ in s, ψ (unfoldRep Γ Δ' q • τ) := setIntegral_unfold hΔ'neg hs hsm ψ fun q =>
          integrableOn_of_bounded_continuous hψc hψ (by rw [volume_smul_sl]; exact hvol)
    _ = ∫ τ in s, ∑ q, ψ (unfoldRep Γ Δ' q • τ) :=
        (integral_finsetSum _ fun q _ => integrableOn_of_bounded_continuous
          (hψc.comp (continuous_const_smul (unfoldRep Γ Δ' q : GL (Fin 2) ℝ))) (hbdd_comp _ hψ)
          hvol).symm
    _ = ∫ τ in s, petersson k f (∑ q, g ∣[k] (α' * (unfoldRep Γ Δ' q : GL (Fin 2) ℝ))) τ := by
        refine setIntegral_congr_fun hsm fun τ _ => ?_
        rw [petersson_sum_right]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hψdef, petersson_sl_smul, ← SlashAction.slash_mul, hf _ (unfoldRep_mem q)]

end Assembly
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section HeckeSpecialization

open CongruenceSubgroup ModularForm

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  simp [Gamma0_mem]

def heckeAlphaQ (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), 0; 0, (p : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp [hp])

def heckeAlpha'Q (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, (1 : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp [hp])

theorem heckeAlphaQ_map {p : ℕ} (hp : p ≠ 0) :
    (heckeAlphaQ p hp).map (Rat.castHom ℝ) = heckeMatrix p 0 := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, val_heckeMatrix hp]
  fin_cases i <;> fin_cases j <;> simp [heckeAlphaQ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem heckeAlpha'Q_map {p : ℕ} (hp : p ≠ 0) :
    (heckeAlpha'Q p hp).map (Rat.castHom ℝ) = heckeDiagMatrix p := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp [heckeAlpha'Q, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem heckeDiagMatrix_coe_eq_smul_inv {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (heckeMatrix p 0).det.val •
        (((heckeMatrix p 0)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hinv : (((heckeMatrix p 0)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)⁻¹] := by
    rw [Matrix.coe_units_inv, val_heckeMatrix hp]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp']
  rw [hinv, det_heckeMatrix hp, val_heckeDiagMatrix hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp']

theorem finiteIndex_inf_conjGL (N : ℕ) [NeZero N] (gQ : GL (Fin 2) ℚ) :
    (Gamma0 N ⊓ conjGL (Gamma0 N) (gQ.map (Rat.castHom ℝ))).FiniteIndex := by
  haveI := ((Gamma0_is_congruence N).conjGL gQ).finiteIndex
  infer_instance

theorem isArithmetic_conj_Gamma0 (N : ℕ) [NeZero N] (gQ : GL (Fin 2) ℚ) :
    (ConjAct.toConjAct (gQ.map (Rat.castHom ℝ))⁻¹ •
      (Gamma0 N : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  simpa [map_inv] using Subgroup.IsArithmetic.conj (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) gQ⁻¹

theorem cuspForm_slash_invariant {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

theorem petersson_slash_bounded_Gamma0 {N : ℕ} [NeZero N] (k : ℤ) (f g : CuspForm (Gamma0 N) k)
    (gQ : GL (Fin 2) ℚ) :
    ∃ C, ∀ τ, ‖petersson k ((⇑f) ∣[k] (gQ.map (Rat.castHom ℝ))) ⇑g τ‖ ≤ C := by
  haveI := isArithmetic_conj_Gamma0 N gQ
  exact petersson_bounded_of_cuspForm k (CuspForm.translate f (gQ.map (Rat.castHom ℝ))) g

theorem petersson_slash_bounded_Gamma0' {N : ℕ} [NeZero N] (k : ℤ) (f g : CuspForm (Gamma0 N) k)
    (gQ : GL (Fin 2) ℚ) :
    ∃ C, ∀ τ, ‖petersson k ⇑f ((⇑g) ∣[k] (gQ.map (Rat.castHom ℝ))) τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := petersson_slash_bounded_Gamma0 k g f gQ
  exact ⟨C, fun τ => by rw [petersson_norm_symm]; exact hC τ⟩

theorem setIntegral_petersson_heckeT_symm {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {s : Set ℍ} (hsm : MeasurableSet s) (hvol : volume s < ⊤)
    (hs : IsFundamentalDomain (PΓ (Gamma0 N)) s (volume : Measure ℍ))
    {Δ Δ' : Subgroup SL(2, ℤ)} (hΔ : Δ = Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0))
    (hΔ' : Δ' = Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p))
    [Fintype (Gamma0 N ⧸ Δ.subgroupOf (Gamma0 N))] [Fintype (Gamma0 N ⧸ Δ'.subgroupOf (Gamma0 N))]
    (hT : ∀ φ : ℍ → ℂ, (∀ γ ∈ Gamma0 N, φ ∣[k] (γ : GL (Fin 2) ℝ) = φ) →
      heckeT k p φ = ∑ q, φ ∣[k] (heckeMatrix p 0 * (unfoldRep (Gamma0 N) Δ q : GL (Fin 2) ℝ)))
    (hT' : ∀ φ : ℍ → ℂ, (∀ γ ∈ Gamma0 N, φ ∣[k] (γ : GL (Fin 2) ℝ) = φ) →
      heckeT k p φ = ∑ q, φ ∣[k] (heckeDiagMatrix p * (unfoldRep (Gamma0 N) Δ' q : GL (Fin 2) ℝ)))
    (f g : CuspForm (Gamma0 N) k) :
    ∫ τ in s, petersson k (heckeT k p ⇑f) ⇑g τ = ∫ τ in s, petersson k ⇑f (heckeT k p ⇑g) τ := by
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [hT ⇑f (cuspForm_slash_invariant f), hT' ⇑g (cuspForm_slash_invariant g)]
  have hφ := petersson_slash_bounded_Gamma0 k f g (heckeAlphaQ p hp0)
  have hψ := petersson_slash_bounded_Gamma0' k f g (heckeAlpha'Q p hp0)
  rw [heckeAlphaQ_map] at hφ
  rw [heckeAlpha'Q_map] at hψ
  exact setIntegral_petersson_doubleCoset_symm (neg_one_mem_Gamma0 N) (det_heckeMatrix_pos p 0)
    (heckeDiagMatrix_coe_eq_smul_inv hp0) hΔ hΔ' hsm hvol hs k (ModularFormClass.continuous f)
    (ModularFormClass.continuous g) (cuspForm_slash_invariant f) (cuspForm_slash_invariant g) hφ hψ

theorem setIntegral_petersson_heckeT_symm' {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {s : Set ℍ} (hsm : MeasurableSet s) (hvol : volume s < ⊤)
    (hs : IsFundamentalDomain (PΓ (Gamma0 N)) s (volume : Measure ℍ))
    (f g : CuspForm (Gamma0 N) k) :
    ∫ τ in s, petersson k (heckeT k p ⇑f) ⇑g τ = ∫ τ in s, petersson k ⇑f (heckeT k p ⇑g) τ := by
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0)).FiniteIndex := by
    rw [← heckeAlphaQ_map hp0]; exact finiteIndex_inf_conjGL N _
  haveI : (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p)).FiniteIndex := by
    rw [← heckeAlpha'Q_map hp0]; exact finiteIndex_inf_conjGL N _
  letI := Subgroup.fintypeQuotientOfFiniteIndex
    (H := (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeMatrix p 0)).subgroupOf (Gamma0 N))
  letI := Subgroup.fintypeQuotientOfFiniteIndex
    (H := (Gamma0 N ⊓ conjGL (Gamma0 N) (heckeDiagMatrix p)).subgroupOf (Gamma0 N))
  exact setIntegral_petersson_heckeT_symm k hp hpN hsm hvol hs rfl rfl
    (fun φ hφ => heckeT_eq_sum_unfold hp hpN k φ hφ)
    (fun φ hφ => heckeT_eq_sum_unfold_diag hp hpN k φ hφ) f g

theorem setIntegral_gammaFD'_petersson_heckeT_symm {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hvol : volume (gammaFD' (Gamma0 N)) < ⊤) (f g : CuspForm (Gamma0 N) k) :
    ∫ τ in gammaFD' (Gamma0 N), petersson k (heckeT k p ⇑f) ⇑g τ =
      ∫ τ in gammaFD' (Gamma0 N), petersson k ⇑f (heckeT k p ⇑g) τ :=
  setIntegral_petersson_heckeT_symm' k hp hpN (measurableSet_gammaFD' _) hvol
    (isFundamentalDomain_gammaFD' _ (neg_one_mem_Gamma0 N)) f g

end HeckeSpecialization
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

end PeterssonAdjoint
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section PeterssonProduct

open MeasureTheory Set ModularGroup UpperHalfPlane Complex CongruenceSubgroup
open scoped Modular MatrixGroups ComplexConjugate Pointwise NNReal ENNReal

scoped instance : SMulInvariantMeasure SL(2, ℤ) ℍ (volume : Measure ℍ) where
  measure_preimage_smul g s hs := by
    simp only [MulAction.compHom_smul_def]
    exact SMulInvariantMeasure.measure_preimage_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) hs

scoped instance : (volume : Measure ℍ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himage_open : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have hpos : 0 < volume (UpperHalfPlane.coe '' U) :=
    himage_open.measure_pos volume (hUne.image _)
  have hmeas : Measurable fun z : ℂ => ((((1 : ℝ≥0) / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    fun_prop
  refine ((MeasureTheory.setLIntegral_pos_iff hmeas).mpr ?_).ne'
  refine hpos.trans_le (measure_mono fun w hw => ?_)
  obtain ⟨τ, hτU, rfl⟩ := hw
  refine ⟨?_, ⟨τ, hτU, rfl⟩⟩
  rw [Function.mem_support]
  simpa using τ.im_ne_zero

scoped instance : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    show Continuous fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z
    exact continuous_const_smul _

private def band (A a : ℝ) (n : ℕ) : Set ℍ :=
  {z : ℍ | |z.re| ≤ A ∧ a * 2 ^ n ≤ z.im ∧ z.im ≤ a * 2 ^ (n + 1)}

private theorem verticalStrip_subset_iUnion_band (A : ℝ) {a : ℝ} (ha : 0 < a) :
    UpperHalfPlane.verticalStrip A a ⊆ ⋃ n : ℕ, band A a n := by
  rintro z ⟨hre, him⟩
  have hex : ∃ n : ℕ, z.im ≤ a * 2 ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (z.im / a) (one_lt_two (α := ℝ))
    exact ⟨n, by
      rw [div_lt_iff₀ ha] at hn
      nlinarith [pow_pos (zero_lt_two (α := ℝ)) n, pow_succ (2 : ℝ) n]⟩
  classical
  refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · exact hre
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hsucc
  · rw [h0]; simpa using him
  · rw [hsucc]
    exact le_of_lt (not_le.mp (Nat.find_min hex (m := Nat.find hex - 1) (by omega)))

private def cbox (relo rehi imlo imhi : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Icc relo rehi ×ˢ Set.Icc imlo imhi)

private lemma mem_cbox {relo rehi imlo imhi : ℝ} {w : ℂ} :
    w ∈ cbox relo rehi imlo imhi ↔
      (relo ≤ w.re ∧ w.re ≤ rehi) ∧ imlo ≤ w.im ∧ w.im ≤ imhi := by
  simp only [cbox, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
    Set.mem_Icc]

private lemma volume_cbox (relo rehi imlo imhi : ℝ) :
    volume (cbox relo rehi imlo imhi) =
      ENNReal.ofReal (rehi - relo) * ENNReal.ofReal (imhi - imlo) := by
  rw [cbox, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

private theorem volume_band_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (n : ℕ) :
    volume (band A a n) ≤ ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) := by
  have h2n : (0 : ℝ) < a * 2 ^ n := by positivity
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himg : (UpperHalfPlane.coe '' band A a n) ⊆
      cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)) := by
    rintro w ⟨z, ⟨hre, him₁, him₂⟩, rfl⟩
    rw [mem_cbox, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    exact ⟨abs_le.mp hre, him₁, him₂⟩
  refine le_trans (lintegral_mono_set himg) ?_
  have hbound : ∀ w ∈ cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)),
      (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal ((a * 2 ^ n)⁻¹ ^ 2) := by
    intro w hw
    obtain ⟨-, him₁, -⟩ := mem_cbox.mp hw
    have hwim : (0 : ℝ) < w.im := lt_of_lt_of_le h2n him₁
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hwim]
    have : (a * 2 ^ n)⁻¹ ^ 2 = (1 / (a * 2 ^ n)) ^ 2 := by rw [one_div]
    rw [this]; gcongr
  refine le_trans (setLIntegral_mono measurable_const hbound) ?_
  rw [setLIntegral_const, volume_cbox]
  rw [show A - -A = 2 * A by ring, show a * 2 ^ (n + 1) - a * 2 ^ n = a * 2 ^ n by ring,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [show (a * 2 ^ n)⁻¹ ^ 2 * (2 * A * (a * 2 ^ n)) =
        2 * A * ((a * 2 ^ n)⁻¹ ^ 2 * (a * 2 ^ n)) by ring,
    pow_two, mul_assoc ((a * 2 ^ n)⁻¹), inv_mul_cancel₀ h2n.ne', mul_one, mul_inv, ← inv_pow]
  norm_num

theorem volume_verticalStrip_lt_top (A : ℝ) {a : ℝ} (ha : 0 < a) :
    volume (UpperHalfPlane.verticalStrip A a) < ⊤ := by
  rcases le_or_gt 0 A with hA | hA
  swap
  · have hempty : UpperHalfPlane.verticalStrip A a = ∅ := by
      ext z; simp only [Set.mem_empty_iff_false, iff_false]
      intro hz; exact absurd hz.1 (not_le.mpr (lt_of_lt_of_le hA (abs_nonneg _)))
    rw [hempty]; simp
  calc volume (UpperHalfPlane.verticalStrip A a)
      ≤ volume (⋃ n : ℕ, band A a n) :=
        measure_mono (verticalStrip_subset_iUnion_band A ha)
    _ ≤ ∑' n : ℕ, volume (band A a n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) :=
        ENNReal.tsum_le_tsum fun n => volume_band_le hA ha n
    _ = ∑' n : ℕ, ENNReal.ofReal (2 * A * a⁻¹) * ENNReal.ofReal ((1 / 2) ^ n) :=
        tsum_congr fun n => by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2) ^ n) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal (1 / 2) ^ n :=
        congrArg _ (tsum_congr fun n => ENNReal.ofReal_pow (by norm_num) n)
    _ = ENNReal.ofReal (2 * A * a⁻¹) * (1 - ENNReal.ofReal (1 / 2))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
        exact ENNReal.ofReal_lt_one.mpr (by norm_num)

theorem fd_subset_verticalStrip : 𝒟 ⊆ UpperHalfPlane.verticalStrip (1 / 2) (1 / 2) := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

theorem volume_fd_lt_top : volume 𝒟 < ⊤ :=
  lt_of_le_of_lt (measure_mono fd_subset_verticalStrip)
    (volume_verticalStrip_lt_top (1 / 2) (by norm_num))

theorem volume_biUnion_smul_fd_lt_top (S : Finset SL(2, ℤ)) :
    volume (⋃ γ ∈ S, γ • 𝒟) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le S _) ?_
  rw [ENNReal.sum_lt_top]
  intro γ _; rw [volume_smul_sl]; exact volume_fd_lt_top

abbrev gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) : Set ℍ := gammaFD' Γ

theorem gammaFundamentalSet_eq_biUnion (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
    gammaFundamentalSet Γ =
      ⋃ γ ∈ (Finset.univ.image fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹), γ • 𝒟 := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  ext z
  simp only [gammaFundamentalSet, gammaFD', Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨fun ⟨q, hq⟩ => ⟨_, ⟨q, rfl⟩, hq⟩, fun ⟨γ, ⟨q, hq⟩, hz⟩ => ⟨q, hq ▸ hz⟩⟩

theorem volume_gammaFundamentalSet_lt_top (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] : volume (gammaFundamentalSet Γ) < ⊤ := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  rw [gammaFundamentalSet_eq_biUnion Γ]
  exact volume_biUnion_smul_fd_lt_top _

theorem smul_fdo_subset_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) :
    (Quotient.out q)⁻¹ • ModularGroup.fdo ⊆ gammaFundamentalSet Γ :=
  Set.Subset.trans (Set.smul_set_mono ModularGroup.fdo_subset_fd)
    (Set.subset_iUnion (fun q' : SL(2, ℤ) ⧸ Γ => (Quotient.out q')⁻¹ • 𝒟) q)

scoped instance instFiniteQuotientGamma0 (N : ℕ) [NeZero N] :
    Finite (SL(2, ℤ) ⧸ (Gamma0 N)) :=
  Subgroup.finite_quotient_of_finiteIndex

theorem volume_gamma0_lt_top (N : ℕ) [NeZero N] :
    volume (gammaFundamentalSet (Gamma0 N)) < ⊤ :=
  volume_gammaFundamentalSet_lt_top (Gamma0 N)

def peterssonInner (k : ℤ) (D : Set ℍ) (f f' : ℍ → ℂ) : ℂ :=
  ∫ τ in D, petersson k f f' τ

theorem petersson_self_eq_ofReal (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    petersson k f f τ = ((Complex.normSq (f τ) * (τ.im : ℝ) ^ k : ℝ) : ℂ) := by
  rw [petersson, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul, Complex.ofReal_zpow]

theorem petersson_self_nonneg (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    0 ≤ Complex.normSq (f τ) * (τ.im : ℝ) ^ k :=
  mul_nonneg (Complex.normSq_nonneg _) (zpow_pos τ.im_pos k).le

theorem peterssonInner_symm (k : ℤ) (D : Set ℍ) (f f' : ℍ → ℂ) :
    peterssonInner k D f' f = conj (peterssonInner k D f f') := by
  unfold peterssonInner
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ => petersson_symm k f f' τ)

theorem peterssonInner_self_eq_ofReal (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    peterssonInner k D f f =
      ((∫ τ in D, Complex.normSq (f τ) * (τ.im : ℝ) ^ k : ℝ) : ℂ) := by
  unfold peterssonInner
  trans (∫ τ in D, ((Complex.normSq (f τ) * (τ.im : ℝ) ^ k : ℝ) : ℂ))
  · exact integral_congr_ae (Filter.Eventually.of_forall fun τ => petersson_self_eq_ofReal k f τ)
  · exact integral_ofReal

theorem peterssonInner_self_re_nonneg (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    0 ≤ (peterssonInner k D f f).re := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun τ => petersson_self_nonneg k f τ

theorem integrableOn_petersson_of_norm_le {k : ℤ} {f f' : ℍ → ℂ} {C : ℝ}
    (hcont : Continuous (petersson k f f')) (hC : ∀ τ, ‖petersson k f f' τ‖ ≤ C)
    {D : Set ℍ} (hD : volume D ≠ ⊤) :
    IntegrableOn (petersson k f f') D := by
  refine (MeasureTheory.integrableOn_const (C := C) hD (by finiteness)).mono'
    hcont.aestronglyMeasurable.restrict ?_
  exact Filter.Eventually.of_forall fun τ => hC τ

theorem integrableOn_petersson_cuspForm (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ))
    [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    {D : Set ℍ} (hD : volume D ≠ ⊤) :
    IntegrableOn (petersson k (⇑f) (⇑f')) D := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  exact integrableOn_petersson_of_norm_le
    (petersson_continuous k (ModularFormClass.holo (F := F) f).continuous
      (ModularFormClass.holo (F := F') f').continuous) hC hD

theorem peterssonInner_add_right {k : ℤ} {D : Set ℍ} {f f' f'' : ℍ → ℂ}
    (h' : IntegrableOn (petersson k f f') D) (h'' : IntegrableOn (petersson k f f'') D) :
    peterssonInner k D f (f' + f'') = peterssonInner k D f f' + peterssonInner k D f f'' := by
  unfold peterssonInner
  rw [← MeasureTheory.integral_add h' h'']
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [petersson, Pi.add_apply]; ring

theorem peterssonInner_add_left {k : ℤ} {D : Set ℍ} {f f' g : ℍ → ℂ}
    (hf : IntegrableOn (petersson k g f) D) (hf' : IntegrableOn (petersson k g f') D) :
    peterssonInner k D (f + f') g = peterssonInner k D f g + peterssonInner k D f' g := by
  rw [peterssonInner_symm, peterssonInner_add_right hf hf', map_add,
    ← peterssonInner_symm, ← peterssonInner_symm]

theorem peterssonInner_smul_left (k : ℤ) (D : Set ℍ) (f f' : ℍ → ℂ) (c : ℂ) :
    peterssonInner k D (c • f) f' = conj c * peterssonInner k D f f' := by
  unfold peterssonInner
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem peterssonInner_self_eq_zero_iff {k : ℤ} {D : Set ℍ} {f : ℍ → ℂ}
    (hint : IntegrableOn (petersson k f f) D) :
    peterssonInner k D f f = 0 ↔ ∀ᵐ τ ∂(volume.restrict D), f τ = 0 := by
  have hreal : IntegrableOn (fun τ => Complex.normSq (f τ) * (τ.im : ℝ) ^ k) D := by
    refine hint.re.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [petersson_self_eq_ofReal k f τ]
    exact Complex.ofReal_re _
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_eq_zero,
    setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun τ => petersson_self_nonneg k f τ) hreal]
  constructor
  · refine fun h => h.mono fun τ hτ => ?_
    rcases mul_eq_zero.mp hτ with h0 | h0
    · exact Complex.normSq_eq_zero.mp h0
    · exact absurd h0 (zpow_pos τ.im_pos k).ne'
  · refine fun h => h.mono fun τ hτ => ?_; simp [hτ]

theorem cuspForm_eq_zero_of_ae_restrict_zero'
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k)
    {D U : Set ℍ} (hU : IsOpen U) (hUne : U.Nonempty) (hUD : U ⊆ D)
    (hae : ∀ᵐ τ ∂(volume.restrict D), f τ = 0) :
    f = 0 := by
  have hae' : ⇑f =ᵐ[volume.restrict U] (0 : ℍ → ℂ) :=
    ae_restrict_of_ae_restrict_of_subset hUD hae
  have heq : Set.EqOn ⇑f 0 U :=
    Measure.eqOn_open_of_ae_eq hae' hU
      (ModularFormClass.continuous f).continuousOn continuousOn_const
  obtain ⟨τ₀, hτ₀⟩ := hUne
  have hfreq : ∃ᶠ z in nhdsWithin τ₀ {τ₀}ᶜ, f z = 0 :=
    ((Filter.eventually_of_mem (hU.mem_nhds hτ₀) fun z hz => heq hz).filter_mono
      nhdsWithin_le_nhds).frequently
  have h0 : ⇑f = 0 := UpperHalfPlane.eq_zero_of_frequently (ModularFormClass.holo f) hfreq
  exact DFunLike.coe_injective (by simpa using h0)

theorem isOpen_smul_fdo (γ : SL(2, ℤ)) : IsOpen ((γ : SL(2,ℤ)) • (𝒟ᵒ : Set ℍ)) := by
  rw [show ((γ : SL(2,ℤ)) • (𝒟ᵒ : Set ℍ)) = (fun z => γ⁻¹ • z) ⁻¹' 𝒟ᵒ by
    ext z; simp [Set.mem_smul_set_iff_inv_smul_mem]]
  exact ModularGroup.isOpen_fdo.preimage (continuous_const_smul _)

theorem two_I_mem_fdo : (⟨2 * Complex.I, by simp⟩ : ℍ) ∈ 𝒟ᵒ := by
  constructor
  · show (1 : ℝ) < Complex.normSq ((_ : ℂ)); simp [Complex.normSq_apply]; norm_num
  · show |(_ : ℂ).re| < (1 : ℝ) / 2; simp

theorem fdo_nonempty : (𝒟ᵒ : Set ℍ).Nonempty := ⟨_, two_I_mem_fdo⟩

variable {N : ℕ} [NeZero N] {k : ℤ}

local notation "Γ₀GL" => ((Gamma0 N : Subgroup SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem integrableOn_petersson_cuspForm_gamma0 {D : Set ℍ} (hD : volume D ≠ ⊤)
    (f g : CuspForm Γ₀GL k) :
    IntegrableOn (petersson k (⇑f) (⇑g)) D :=
  integrableOn_petersson_cuspForm k Γ₀GL f g hD

@[reducible] def peterssonCore (D : Set ℍ) (hD : volume D ≠ ⊤)
    (hdef : ∀ f : CuspForm Γ₀GL k, peterssonInner k D (⇑f) (⇑f) = 0 → f = 0) :
    InnerProductSpace.Core ℂ (CuspForm Γ₀GL k) where
  inner f g := peterssonInner k D (⇑f) (⇑g)
  conj_inner_symm f g := (peterssonInner_symm k D (⇑g) (⇑f)).symm
  re_inner_nonneg f := peterssonInner_self_re_nonneg k D (⇑f)
  add_left f g h := by
    show peterssonInner k D ⇑(f + g) ⇑h = _
    rw [CuspForm.coe_add]
    exact peterssonInner_add_left (integrableOn_petersson_cuspForm_gamma0 hD h f)
      (integrableOn_petersson_cuspForm_gamma0 hD h g)
  smul_left f g c := by
    show peterssonInner k D ⇑(c • f) ⇑g = _
    rw [show (⇑(c • f) : ℍ → ℂ) = c • ⇑f from rfl]
    exact peterssonInner_smul_left k D (⇑f) (⇑g) c
  definite f hf := hdef f hf

theorem peterssonCore_inner (D : Set ℍ) (hD : volume D ≠ ⊤) (hdef)
    (f g : CuspForm Γ₀GL k) :
    (peterssonCore D hD hdef).inner f g = peterssonInner k D (⇑f) (⇑g) := rfl

@[reducible] def peterssonCoreGamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    InnerProductSpace.Core ℂ
      (CuspForm ((Gamma0 N : Subgroup SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :=
  let D := gammaFundamentalSet (Gamma0 N)
  peterssonCore D (volume_gamma0_lt_top N).ne <| fun f hf => by
    have hint : IntegrableOn (petersson k (⇑f) (⇑f)) D :=
      integrableOn_petersson_cuspForm_gamma0 (volume_gamma0_lt_top N).ne f f
    have hae := (peterssonInner_self_eq_zero_iff hint).mp hf
    set q₀ : SL(2, ℤ) ⧸ (Gamma0 N) := QuotientGroup.mk 1
    exact cuspForm_eq_zero_of_ae_restrict_zero' f
      (U := (Quotient.out q₀)⁻¹ • 𝒟ᵒ) (isOpen_smul_fdo _)
      (fdo_nonempty.smul_set)
      (smul_fdo_subset_gammaFundamentalSet (Gamma0 N) q₀) hae

theorem peterssonCoreGamma0_inner (N : ℕ) [NeZero N] (k : ℤ)
    (f g : CuspForm ((Gamma0 N : Subgroup SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    (peterssonCoreGamma0 N k).inner f g =
      peterssonInner k (gammaFundamentalSet (Gamma0 N)) (⇑f) (⇑g) := rfl

end PeterssonProduct
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section HeckeAdjointDock

open MeasureTheory CongruenceSubgroup
open scoped MatrixGroups

theorem heckeTLin_petersson_symm (N : ℕ) [NeZero N] (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (v w : CuspForm (Gamma0 N) k) :
    (peterssonCoreGamma0 N k).inner (CuspForm.heckeTLin k hℓ hℓN v) w =
      (peterssonCoreGamma0 N k).inner v (CuspForm.heckeTLin k hℓ hℓN w) := by
  rw [peterssonCoreGamma0_inner, peterssonCoreGamma0_inner, CuspForm.coe_heckeTLin_apply,
    CuspForm.coe_heckeTLin_apply]
  exact setIntegral_gammaFD'_petersson_heckeT_symm k hℓ hℓN (volume_gamma0_lt_top N) v w

end HeckeAdjointDock
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

section Assembly

open CongruenceSubgroup

theorem heckeAlgebraReduced :
    ∀ (N : ℕ) [NeZero N] (S : Set ℕ), (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) →
      IsReduced (CuspForm.heckeAlgebra N 2 S) := by
  intro N _ S hNS
  haveI : FiniteDimensional ℂ (CuspForm (Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2
  exact heckeAlgebra_isReduced_of_core_anemic N 2 S hNS (peterssonCoreGamma0 N 2)
    (fun ℓ hℓ hℓN _ v w => heckeTLin_petersson_symm N 2 ℓ hℓ hℓN v w)

end Assembly
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ"

end H6
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6"

end
p2m_reactivate "P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6.PΓ P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.H6"

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) :
    IsReduced (CuspForm.heckeAlgebra N 2 S) :=
  H6.heckeAlgebraReduced N S hNS

end S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset
end P2MW
export P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset (solution)
