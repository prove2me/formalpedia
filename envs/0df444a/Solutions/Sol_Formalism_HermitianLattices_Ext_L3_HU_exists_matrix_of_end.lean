-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_matrix_of_end
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:26.380168+00:00
-- url     : https://prove2.me/submissions/b3abead8-84e1-4747-b7f3-e8964f88bf29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) : ∃ Y : Matrix κ κ (𝓞 K),
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩
    | mul x x' _ _ hx hx' =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hx'
      exact ⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩
  have surj : ∀ z : QA 𝔭 b k, ∃ w : spanO b, Submodule.Quotient.mk (inA 𝔭 b w) = z := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
        s • (y : V) ∈ spanO b := y.2
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, rfl⟩ := key s hs
    obtain ⟨y', i, hi, hyi⟩ := h𝔭.exists_inv ht
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 F) i k
    have e0 : (1 : 𝓞 F) - i = y' * t := by linear_combination -hyi
    rw [e0, one_pow] at hq
    have hc : ι (y' * q) * ι t = 1 - ι (i ^ k) := by
      have h2 := congrArg ι hq
      simp only [map_sub, map_one, map_mul, map_pow] at h2 ⊢
      linear_combination -h2
    have hmem : ι (i ^ k) ∈ extP K 𝔭 ^ k := by
      rw [map_pow]
      exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
    refine ⟨⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩, ?_⟩
    rw [Submodule.Quotient.eq]
    have e4 : inA 𝔭 b ⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩ - y =
        (-ι (i ^ k)) • y := by
      apply Subtype.ext
      show ι (y' * q) • (ι t • (y : V)) - (y : V) = (-ι (i ^ k)) • (y : V)
      rw [smul_smul, hc, sub_smul, one_smul, neg_smul]
      abel
    rw [e4]
    exact Submodule.smul_mem_smul (Submodule.neg_mem _ hmem) Submodule.mem_top
  have hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w := by
    intro w
    unfold cmb
    exact (Basis.equivFun _).symm.surjective w
  choose w hw using surj
  choose c hc' using hc
  refine ⟨Matrix.of fun l i => c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l,
    fun i => ?_⟩
  have e : (cmb b fun l => Matrix.of (fun l i =>
      c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l) l i) =
      w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1))))) := by
    simp only [Matrix.of_apply]
    exact hc' _
  rw [e, hw]
end Formalism.HermitianLattices.Ext.L3.HU
