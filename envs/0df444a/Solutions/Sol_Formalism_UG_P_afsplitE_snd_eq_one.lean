-- Prove2me | solution 1 for Formalism.UG.P.afsplitE_snd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:03.528558+00:00
-- url     : https://prove2.me/submissions/4aeacb22-c6dd-4222-ba9e-40c23e8ecde9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplitE_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Lat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end Lat
section Int
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
variable {n : Type} [Fintype n] [DecidableEq n]
end Int
section Iso
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
private lemma prV_IE_ne_lemma_16 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) w (afsplitIE v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [IE_tmul_lemma_10, prV_tmul_lemma_12, afsplitF_ne v w hw, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
private lemma eps_ne_lemma_17 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) : prV (E := E) w (afsplitEps E v) = 0 := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl]
  exact prV_IE_ne_lemma_16 v w hw 1
private lemma C_map_ne_lemma_15 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸)) :
    (afsplitC v M N).map (prV (E := E) w) = N.map (prV (E := E) w) := by
  ext i j
  simp only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, prV_IE_ne_lemma_16 v w hw, eps_ne_lemma_17 v w hw, sub_zero, one_mul, zero_add]
private lemma Z_lemma_14 (z : E ⊗[F] 𝔸)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → prV (E := E) w z = 0) :
    (1 - afsplitEps E v) * z = 0 := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left (Module.Basis.ofVectorSpace F E) z
  have hcw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → ∀ i, (c i) w = 0 := by
    intro w hw i
    have h0 := hz w hw
    have hmap : prV (E := E) w (c.sum fun i n => (Module.Basis.ofVectorSpace F E) i ⊗ₜ[F] n) =
        (Finsupp.mapRange (evalV F w) (map_zero _) c).sum
          (fun i n => (Module.Basis.ofVectorSpace F E) i ⊗ₜ[F] n) := by
      rw [Finsupp.sum_mapRange_index (fun i => by simp)]
      first | rw [map_finsuppSum] | rw [map_finsupp_sum]
      simp only [prV_tmul_lemma_12]
      try rfl
    rw [hmap] at h0
    have h1 := TensorProduct.sum_tmul_basis_left_eq_zero (Module.Basis.ofVectorSpace F E) _ h0
    have h2 := DFunLike.congr_fun h1 i
    have h3 : (evalV F w) (c i) = 0 := by simpa using h2
    exact h3
  have key : ∀ i, (1 - afsplitF v 1) * c i = 0 := by
    intro i
    ext w
    congr 1
    rw [show ((1 - afsplitF v 1) * c i) w = (1 - afsplitF v 1 w) * (c i) w from by first | rfl | simp]
    rw [show (0 : 𝔸) w = 0 from by first | rfl | simp]
    by_cases h : w = v
    · subst h
      rw [afsplitF_self, sub_self, zero_mul]
    · rw [hcw w h i, mul_zero]
  have h1 : (1 : E ⊗[F] 𝔸) - afsplitEps E v = (1 : E) ⊗ₜ[F] (1 - afsplitF v 1) := by
    rw [eps_eq_lemma_2, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
  rw [h1, Finsupp.mul_sum]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, key i, TensorProduct.tmul_zero]
end Iso
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (g : UPts σ J 𝔸) :
    (afsplitE σ J v g).2 = 1 ↔ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (g : GL n (E ⊗[F] 𝔸)) = 1 := by
  have e : (afsplitE σ J v g).2 = 1 ↔ afsplitU v 1 (g : GL n (E ⊗[F] 𝔸)) = 1 := by
    rw [← afsplitE_snd σ J v g]
    exact ⟨fun h => by simp [h], fun h => by
      first | exact Subtype.ext h | exact OneMemClass.coe_eq_one.mp h | simpa using h⟩
  rw [e]
  constructor
  · intro h w hw
    apply Units.ext
    rw [afsplit_coe_bc_prV]
    rw [← C_map_ne_lemma_15 v w hw (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸))]
    have h' : afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) = 1 := by
      have h3 := congrArg (fun M : GL n (E ⊗[F] 𝔸) => (M : Matrix n n (E ⊗[F] 𝔸))) h
      exact h3
    rw [h', Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  · intro h
    apply Units.ext
    show afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) = 1
    ext i j
    have hz : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
        prV (E := E) w (((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j - (1 : Matrix n n (E ⊗[F] 𝔸)) i j) = 0 := by
      intro w hw
      have hw' := congrArg (fun M : GL n (E ⊗[F] w.adicCompletion F) =>
        (M : Matrix n n (E ⊗[F] w.adicCompletion F)) i j) (h w hw)
      simp only [afsplit_coe_bc_prV, Matrix.map_apply, Units.val_one] at hw'
      rw [map_sub, hw', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hZ := Z_lemma_14 v _ hz
    have hI : afsplitIE v ((1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) =
        afsplitEps E v * (1 : Matrix n n (E ⊗[F] 𝔸)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact (mul_one (afsplitEps E v)).symm
      · rw [map_zero, mul_zero]
    simp only [afsplitC, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hI]
    linear_combination hZ
end Formalism.UG.P
