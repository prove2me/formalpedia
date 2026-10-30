-- Prove2me | solution 1 for DiazModulus.exists_isRegular_quotient_ofList
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T18:21:28.644946+00:00
-- url     : https://prove2.me/submissions/d927deab-7e9a-4d1e-9ee1-dbfd54bad20c

import Mathlib

open RingTheory.Sequence IsLocalRing Pointwise CategoryTheory CategoryTheory.Limits Abelian

universe u

/-! # A long regular sequence survives the quotient by a weakly regular one, over a local ring

Induction on `ps`, one element `p ∈ 𝔪` at a time, with `M` replaced by `M/pM`, which is again finite
and, by Nakayama (`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`), nontrivial. The step: if
`M` has a regular sequence of length `n + 1` in `𝔪`, then `M/pM` has one of length `n`. Rees' theorem
(`ModuleCat.exists_isRegular_tfae`, with `𝔪M ≠ M`) turns the regular sequence into the vanishing of
`Ext^i(A/𝔪, M)` for `i ≤ n`; the covariant long exact `Ext` sequence of the short exact sequence
`0 → M → M → M/pM → 0` given by multiplication by `p` (`Ext.covariant_sequence_exact₃'`, with
`IsSMulRegular.smulShortComplex_shortExact`) gives `Ext^i(A/𝔪, M/pM) = 0` for `i < n`; Rees' theorem
again gives a regular sequence of length `n` in `𝔪` on `M/pM`. Finally `M/(p :: ps)M` is
`(M/pM)/(ps)(M/pM)` (`Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner`), and regularity is
carried by linear equivalences. -/

namespace C12_DQ

section
variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Nakayama: `𝔪M < M` for a nontrivial finite module over a local ring. -/
lemma smul_top_lt_top (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] : (maximalIdeal A) • (⊤ : Submodule A M) < ⊤ :=
  (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson _)).lt_top'

/-- Nakayama: the quotient by an element of the maximal ideal stays nontrivial. -/
lemma nontrivial_quotSMulTop (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] {x : A} (hx : x ∈ maximalIdeal A) : Nontrivial (QuotSMulTop x M) := by
  refine Submodule.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (smul_top_lt_top M).ne ?_)
  rw [← Submodule.ideal_span_singleton_smul]
  exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hx)

omit [IsLocalRing A] in
/-- The covariant long exact `Ext` sequence of `0 → M →x→ M → M/xM → 0`: vanishing of
`Ext^i(N, M)` for `i ≤ n` gives vanishing of `Ext^i(N, M/xM)` for `i < n`. -/
lemma subsingleton_ext_quotSMulTop (N : ModuleCat.{u} A) (M : Type u) [AddCommGroup M]
    [Module A M] {x : A} (hx : IsSMulRegular M x) (n : ℕ)
    (h : ∀ i < n + 1, Subsingleton (Ext N (ModuleCat.of A M) i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of A (QuotSMulTop x M)) i) := by
  intro i hi
  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of A M) hx
  have z2 : IsZero (AddCommGrpCat.of (Ext N (ModuleCat.of A M) i)) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have z1 : IsZero (AddCommGrpCat.of (Ext N (ModuleCat.of A M) (i + 1))) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl)
    (z2.eq_zero_of_src _) (z1.eq_zero_of_tgt _)

variable [IsNoetherianRing A]

/-- One step, through Rees' theorem: a regular sequence of length `m + 1` in `𝔪` on `M` gives one
of length `m` on `M/xM`, for `x ∈ 𝔪` regular on `M`. -/
lemma exists_isRegular_quotSMulTop (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] {x : A} (hx : IsSMulRegular M x)
    (hxm : x ∈ maximalIdeal A) (zs : List A) (hz : IsRegular M zs)
    (hzm : ∀ z ∈ zs, z ∈ maximalIdeal A) :
    ∃ ts : List A, zs.length ≤ ts.length + 1 ∧ (∀ t ∈ ts, t ∈ maximalIdeal A) ∧
      IsRegular (QuotSMulTop x M) ts := by
  have := nontrivial_quotSMulTop M hxm
  rcases Nat.eq_zero_or_pos zs.length with h0 | hpos
  · exact ⟨[], by omega, by simp, IsRegular.nil A _⟩
  have T := ModuleCat.exists_isRegular_tfae (maximalIdeal A) zs.length (ModuleCat.of A M)
    (smul_top_lt_top M)
  have hext : ∀ i < zs.length, Subsingleton (Ext (ModuleCat.of A (Shrink.{u} (A ⧸ maximalIdeal A)))
      (ModuleCat.of A M) i) := (T.out 3 1).mp (show ∃ rs : List A, rs.length = zs.length ∧
        (∀ r ∈ rs, r ∈ maximalIdeal A) ∧ IsRegular (ModuleCat.of A M) rs from ⟨zs, rfl, hzm, hz⟩)
  have hext' := subsingleton_ext_quotSMulTop _ M hx (zs.length - 1)
    (fun i (hi : i < zs.length - 1 + 1) => hext i (by omega))
  obtain ⟨ts, hlen, hts, hreg⟩ := ((ModuleCat.exists_isRegular_tfae (maximalIdeal A)
    (zs.length - 1) (ModuleCat.of A (QuotSMulTop x M)) (smul_top_lt_top _)).out 1 3).mp hext'
  exact ⟨ts, by omega, hts, hreg⟩

/-- The statement, with `M` quantified after `ps` for the induction. -/
lemma dq_aux (ps : List A) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M],
      IsWeaklyRegular M ps → (∀ p ∈ ps, p ∈ maximalIdeal A) →
      ∀ zs : List A, IsRegular M zs → (∀ z ∈ zs, z ∈ maximalIdeal A) →
      ∃ ts : List A, zs.length ≤ ts.length + ps.length ∧ (∀ t ∈ ts, t ∈ maximalIdeal A) ∧
        IsRegular (M ⧸ (Ideal.ofList ps • (⊤ : Submodule A M))) ts := by
  induction ps with
  | nil =>
    intro M _ _ _ _ _ _ zs hz hzm
    have hbot : Ideal.ofList ([] : List A) • (⊤ : Submodule A M) = ⊥ := by simp
    exact ⟨zs, by simp, hzm,
      ((Submodule.quotEquivOfEqBot _ hbot).isRegular_congr zs).mpr hz⟩
  | cons p ps ih =>
    intro M _ _ _ _ hps hpm zs hz hzm
    rw [isWeaklyRegular_cons_iff] at hps
    have hp : p ∈ maximalIdeal A := hpm p (List.mem_cons_self ..)
    have := nontrivial_quotSMulTop M hp
    obtain ⟨zs', hlen', hzm', hz'⟩ := exists_isRegular_quotSMulTop M hps.1 hp zs hz hzm
    obtain ⟨ts, hlen, htm, hts⟩ := ih (QuotSMulTop p M) hps.2
      (fun r hr => hpm r (List.mem_cons_of_mem _ hr)) zs' hz' hzm'
    refine ⟨ts, by simp; omega, htm, ?_⟩
    exact ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M p ps).isRegular_congr
      ts).mpr hts

end

end C12_DQ

open C12_DQ in
theorem solution {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (ps : List A) (hps : RingTheory.Sequence.IsWeaklyRegular M ps) (hpm : ∀ p ∈ ps, p ∈ IsLocalRing.maximalIdeal A)
    (zs : List A) (hz : RingTheory.Sequence.IsRegular M zs) (hzm : ∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal A) :
    ∃ ts : List A, zs.length ≤ ts.length + ps.length ∧ (∀ t ∈ ts, t ∈ IsLocalRing.maximalIdeal A) ∧
      RingTheory.Sequence.IsRegular (M ⧸ (Ideal.ofList ps • (⊤ : Submodule A M))) ts := by
  exact dq_aux ps M hps hpm zs hz hzm
