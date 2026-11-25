-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.completeA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:07.446872+00:00
-- url     : https://prove2.me/submissions/43dcc8fe-abc5-4c0d-a54e-992eb0067967

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := by
  classical
  have key : ∀ (A : Type) [CommRing A] (a x : A) (n : ℕ),
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule A A) ↔ ∃ s, x = a ^ n * s := by
    intro A _ a x n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, -, hs⟩
      exact ⟨s, by rw [← hs, smul_eq_mul]⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, Submodule.mem_top, by rw [hs, smul_eq_mul]⟩
  let bR := Algebra.TensorProduct.basis ℤ_[l] (Module.Free.chooseBasis ℤ OE)
  have hl : ∀ (n : ℕ) (s : ℤ_[l] ⊗[ℤ] OE),
      ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s = ((l : ℤ_[l]) ^ n) • s := by
    intro n s
    rw [Algebra.smul_def, map_pow, map_natCast]
  have hcoord : ∀ (n : ℕ) (x : ℤ_[l] ⊗[ℤ] OE),
      (∃ s, x = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s) ↔ ∀ i, ∃ c, bR.repr x i = (l : ℤ_[l]) ^ n * c := by
    intro n x
    constructor
    · rintro ⟨s, rfl⟩ i
      refine ⟨bR.repr s i, ?_⟩
      rw [hl, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro h
      choose c hc using h
      refine ⟨∑ i, c i • bR i, ?_⟩
      rw [hl]
      apply bR.repr.injective
      ext i
      rw [hc i, LinearEquiv.map_smul, Finsupp.smul_apply, bR.repr_sum_self, smul_eq_mul]
  have hZ : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have haus : ∀ x : ℤ_[l] ⊗[ℤ] OE, (∀ n : ℕ, x ≡ 0 [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
      Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) → x = 0 := by
    intro x hx
    apply bR.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    apply hZ.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    have h := hx n
    rw [SModEq.sub_mem, sub_zero, key, hcoord] at h
    exact h i
  have prec : ∀ f : ℕ → ℤ_[l] ⊗[ℤ] OE, (∀ {m n : ℕ}, m ≤ n → f m ≡ f n
      [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ m • ⊤ : Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) →
      ∃ L, ∀ n, f n ≡ L [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
        Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))] := by
    intro f hf
    have hci : ∀ i, ∃ Li : ℤ_[l], ∀ n, bR.repr (f n) i ≡ Li
        [SMOD (Ideal.span {((l : ℕ) : ℤ_[l])} ^ n • ⊤ : Submodule ℤ_[l] ℤ_[l])] := by
      intro i
      apply hZ.toIsPrecomplete.prec
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, key, hcoord] at h
      rw [SModEq.sub_mem, key]
      obtain ⟨c, hc⟩ := h i
      exact ⟨c, by rw [← hc, map_sub, Finsupp.sub_apply]⟩
    choose L hL using hci
    refine ⟨∑ i, L i • bR i, fun n => ?_⟩
    rw [SModEq.sub_mem, key, hcoord]
    intro i
    have h := hL i n
    rw [SModEq.sub_mem, key] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [map_sub, Finsupp.sub_apply, bR.repr_sum_self, hc]⟩
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨haus⟩
  haveI : IsPrecomplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨fun f hf => prec f hf⟩
  exact IsAdicComplete.mk
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
