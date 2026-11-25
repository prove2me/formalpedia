-- Prove2me | solution 2 for DetDLP.theorem_4_3_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:30:25.507171+00:00
-- url     : https://prove2.me/submissions/20a36bef-23d9-4d75-938b-8b97ecf1e340

import Theorems.Thm_DetDLP_d4_guarded_terminal_from_appendix_d
import Theorems.Thm_DetDLP_section5_guard_and_kronecker

set_option autoImplicit false
set_option maxHeartbeats 200000
open DetDLP Polynomial OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

private theorem f5_log_nat (m : ℕ) (hm : 1 ≤ m) : logSafe m ≤ m := by
  have h : max 2 (m : ℝ) ≤ (2:ℝ)^m := by
    refine max_le ?_ ?_
    · simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm)
    · exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity : 0 < max 2 (m:ℝ)) h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  exact max_le (by exact_mod_cast hm) this

private theorem f5_logs (C b m : ℕ) (hC : 0 < C) (hb : 2 ≤ b) (hm : 1 ≤ m)
    (h : blockCount b ≤ C*m) : logLogSafe b ≤ (4*(C+1):ℕ) * logSafe m := by
  have hL : (Nat.clog 2 (b+2) : ℝ)^((1:ℝ)/4) ≤ (C:ℝ)*m := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans h)
  have hL' := pow_le_pow_left₀ (by positivity) hL 4
  rw [← Real.rpow_mul_natCast (by positivity)] at hL'
  norm_num at hL'
  have hclog : Real.logb 2 (b:ℝ) ≤ Nat.clog 2 (b+2) := by
    calc _ ≤ Real.logb 2 ((b+2:ℕ):ℝ) := Real.logb_le_logb_of_le (by norm_num) (by positivity) (by norm_num)
         _ ≤ _ := by
           rw [← Real.natCeil_logb_natCast]
           simpa only [Nat.cast_ofNat] using (Nat.le_ceil (Real.logb (2:ℝ) (b+2:ℕ)))
  have hcm : (2:ℝ) ≤ (C:ℝ)*m := by exact_mod_cast (le_max_left _ _).trans h
  have hp : (2:ℝ) ≤ ((C:ℝ)*m)^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hcm 4]
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0 < max 2 (Real.logb 2 b)) (max_le hp (hclog.trans hL'))
  rw [Real.logb_pow, Real.logb_mul (by positivity) (by positivity)] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have lelog (n : ℕ) (hn : 0<n) : Real.logb 2 n ≤ logSafe n :=
    (Real.logb_le_logb_of_le (by norm_num) (by positivity) (le_max_right 2 _)).trans (le_max_right _ _)
  have hs : 1 ≤ logSafe m := le_max_left _ _
  have hc := (lelog C hC).trans (f5_log_nat C hC)
  have hd := lelog m hm
  unfold logLogSafe
  rw [max_eq_right hb']
  push_cast
  apply max_le <;> nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (C:ℝ))]

private theorem f5_time (K C b m : ℕ) (hC : 0 < C) (hb : 2 ≤ b) (hm : 1 ≤ m) (h : blockCount b ≤ C*m) :
    (2:ℝ)^((K:ℝ)*((b:ℝ)/m+(b:ℝ)/Real.sqrt (logSafe m))) ≤ mainTimeBound (K*(8*(C+1))) b := by
  let D : ℝ := 4*((C:ℝ)+1)
  have hd : 1 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hs : 1 ≤ logSafe m := le_max_left _ _
  have ht : 1 ≤ logLogSafe b := le_max_left _ _
  have hs' : 0 < Real.sqrt (logSafe m) := Real.sqrt_pos.2 (by linarith)
  have ht' : 0 < Real.sqrt (logLogSafe b) := Real.sqrt_pos.2 (by linarith)
  have hl : logLogSafe b ≤ D*logSafe m := by simpa [D] using f5_logs C b m hC hb hm h
  have hds := Real.sqrt_le_sqrt hl
  rw [Real.sqrt_mul (by linarith : 0 ≤ D)] at hds
  have hds' := hds.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hd)) hs'.le)
  have hms := (Real.sqrt_le_self_iff.mpr (Or.inr hs)).trans (f5_log_nat m hm)
  have u : (b:ℝ)/m ≤ (b:ℝ)/Real.sqrt (logSafe m) := div_le_div_of_nonneg_left (by positivity) hs' hms
  have v : (b:ℝ)/Real.sqrt (logSafe m) ≤ D*b/Real.sqrt (logLogSafe b) := by
    apply (div_le_div_iff₀ hs' ht').2
    nlinarith [mul_le_mul_of_nonneg_left hds' (by positivity : 0≤(b:ℝ))]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  calc _ ≤ (K:ℝ)*(D*b/Real.sqrt (logLogSafe b)+D*b/Real.sqrt (logLogSafe b)) := mul_le_mul_of_nonneg_left (add_le_add (u.trans v) v) (by positivity)
       _ = _ := by dsimp [D]; ring

private theorem f5_guard (P g : ℕ) (z s : ℤ)
    (h : s ≡ (2:ℤ)^g*z [ZMOD (2:ℤ)^(g+P)])
    (clear : ∀ P0 Q r acc : ℕ, r < 2^P0 → acc < 2^(P0+Q) →
      (acc:ℤ) ≡ ((2^Q*r:ℕ):ℤ) [ZMOD ((2^(P0+Q):ℕ):ℤ)] → acc = 2^Q*r ∧ acc/2^Q=r) :
    (s : ZMod (2^(g+P))).val / 2^g = (z : ZMod (2^P)).val := by
  apply (clear P g _ _ (ZMod.val_lt _) (by simpa [Nat.add_comm g P] using ZMod.val_lt (s : ZMod (2^(g+P)))) ?_).2
  push_cast
  rw [Nat.add_comm P g, ZMod.val_intCast, ZMod.val_intCast]
  push_cast
  refine (Int.mod_modEq _ _).trans (h.trans ?_)
  rw [pow_add]
  exact (Int.mod_modEq _ _).symm.mul_left'

private theorem f5_poly (P l : ℕ) (p : ℤ[X]) :
    Ideal.Quotient.mk _ (p.map (Int.castRingHom (ZMod (2^P)))) =
      truncPolyOfCoeffs P l (fun i => (p.coeff i.val : ZMod (2^P)).val) := by
  classical
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  apply X_pow_dvd_iff.mpr
  intro d hd
  let i : Fin l := ⟨d,hd⟩
  rw [coeff_sub, coeff_map, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp [i]
  · intro j _ hj
    simp [coeff_monomial, show j.val ≠ d from fun e => hj (Fin.ext e)]
  · simp


namespace F5Encoding
noncomputable def intPolynomialToTruncPoly (P0 ℓ : ℕ) :
    Polynomial ℤ →+* TruncPoly P0 ℓ :=
  (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ})).comp
    (Polynomial.mapRingHom (Int.castRingHom (ZMod (2 ^ P0))))

/-- The output prescribed by the integer-coefficient schedule represents its quotient value. -/
theorem encodes_intPolynomialToTruncPoly (P0 ℓ : ℕ) (p : Polynomial ℤ) :
    EncodesTruncPoly P0 ℓ
      (encodeNatListBin (List.ofFn fun i : Fin ℓ => (p.coeff i.val : ZMod (2 ^ P0)).val))
      (intPolynomialToTruncPoly P0 ℓ p) := by
  let : NeZero (2 ^ P0) := ⟨by positivity⟩
  refine ⟨fun i => (p.coeff i.val : ZMod (2 ^ P0)).val,
    fun i => ZMod.val_lt _, rfl, ?_⟩
  change Ideal.Quotient.mk _ (p.map (Int.castRingHom (ZMod (2 ^ P0)))) = _
  exact f5_poly P0 ℓ p

/-- Tensor contraction commutes with every ring homomorphism. -/
theorem map_BTNContract {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) :
    f (BTNContract G T) = BTNContract G (fun v α => f (T v α)) := by
  simp only [BTNContract, map_sum, map_prod]

/-- Canonical natural coefficients reduce to the same tensor entry. -/
theorem intPolynomialToTruncPoly_sum_monomial (P0 ℓ : ℕ) (a : Fin ℓ → ℕ) :
    intPolynomialToTruncPoly P0 ℓ
      (∑ i : Fin ℓ, Polynomial.monomial i.val (a i : ℤ)) =
      truncPolyOfCoeffs P0 ℓ a := by
  unfold intPolynomialToTruncPoly truncPolyOfCoeffs
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_sum, Polynomial.map_monomial, Int.coe_castRingHom, Int.cast_natCast]

/-- Integer contraction followed by coefficient reduction gives the required BTN output. -/
theorem encodes_integer_BTNContract (P0 ℓ : ℕ) (G : BipartiteMultigraph)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ → ℕ) :
    let Z := BTNContract G (fun v α => ∑ i : Fin ℓ, Polynomial.monomial i.val (A v α i : ℤ))
    EncodesTruncPoly P0 ℓ
      (encodeNatListBin (List.ofFn fun i : Fin ℓ => (Z.coeff i.val : ZMod (2 ^ P0)).val))
      (BTNContract G (fun v α => truncPolyOfCoeffs P0 ℓ (A v α))) := by
  dsimp only
  have h := encodes_intPolynomialToTruncPoly P0 ℓ
    (BTNContract G (fun v α => ∑ i : Fin ℓ, Polynomial.monomial i.val (A v α i : ℤ)))
  simpa only [map_BTNContract, intPolynomialToTruncPoly_sum_monomial] using h

open OAI.Algorithms.SubexponentialSAT.Computation

/-- An entry evaluator already computes the canonical integer coefficient arrays needed
by the integer-coefficient contraction schedule; no extra decoding machine is required. -/
theorem btnEntryEvaluable_iff_canonical_coefficients
    (desc : List Bool) (G : BipartiteMultigraph) (P0 ℓ : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (τ σ : ℝ) :
    BTNEntryEvaluable desc G P0 ℓ T E outE τ σ ↔
      ∃ A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ → ℕ,
        (∀ v α i, A v α i < 2 ^ P0) ∧
        (∀ v α, T v α = truncPolyOfCoeffs P0 ℓ (A v α)) ∧
        (∀ v α, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn α))
          (encodeNatListBin (List.ofFn (A v α))) τ σ) := by
  classical
  constructor
  · intro h
    have hc : ∀ (v : Fin G.nV) (α : Fin (G.deg v) → Bool),
        ∃ c : Fin ℓ → ℕ, (∀ i, c i < 2 ^ P0) ∧
          T v α = truncPolyOfCoeffs P0 ℓ c ∧
          RunsWithin E outE (encodePortQuery desc v.val (List.ofFn α))
            (encodeNatListBin (List.ofFn c)) τ σ := by
      intro v α
      obtain ⟨w, ⟨c, hc, rfl, hT⟩, hr⟩ := h v α
      exact ⟨c, hc, hT, hr⟩
    choose A hA hT hRun using hc
    exact ⟨A, hA, hT, hRun⟩
  · rintro ⟨A, hA, hT, hRun⟩ v α
    exact ⟨encodeNatListBin (List.ofFn (A v α)),
      ⟨A v α, hA v α, rfl, hT v α⟩, hRun v α⟩

/-- The schedule's exact word is the canonical encoding of the original tensor contraction. -/
theorem encodes_integer_BTNContract_of_entries (P0 ℓ : ℕ) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ → ℕ)
    (hT : ∀ v α, T v α = truncPolyOfCoeffs P0 ℓ (A v α)) :
    let Z := BTNContract G (fun v α => ∑ i : Fin ℓ, Polynomial.monomial i.val (A v α i : ℤ))
    EncodesTruncPoly P0 ℓ
      (encodeNatListBin (List.ofFn fun i : Fin ℓ => (Z.coeff i.val : ZMod (2 ^ P0)).val))
      (BTNContract G T) := by
  have hfun : T = fun v α => truncPolyOfCoeffs P0 ℓ (A v α) := by
    funext v α
    exact hT v α
  rw [hfun]
  exact encodes_integer_BTNContract P0 ℓ G A

end F5Encoding

theorem solution (hOAI : OpenAIAppendixDPremise) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ b →
            1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S →
            1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (polyBound c0 (S + desc.length)) (polyBound c0 (S + desc.length)) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts) w
                (polyBound K (S + desc.length) * mainTimeBound K b)
                (polyBound K (S + desc.length)) := by
  classical
  intro C c0 hC hc E outE
  have hg := section5_guard_and_kronecker
  obtain ⟨M,outM,K,hM⟩ := d4_guarded_terminal_from_appendix_d hOAI C c0 hC hc E outE
  let K' := K*(8*(C+1))
  refine ⟨M,outM,K',?_⟩
  intro b m k S P l desc G T hb hm hk hbm hmb hS hβ hβ' hP hPS hl hlm hV spec he
  obtain ⟨A,hA,hT,hE⟩ := (F5Encoding.btnEntryEvaluable_iff_canonical_coefficients _ _ _ _ _ _ _ _ _).mp he
  obtain ⟨g,n,F,hd,hr⟩ := hM b m k S P l desc G A hb hm hk hbm hmb hS hβ hβ' hP hPS hl hlm hV spec hA hE
  let Z := BTNContract G (fun v t => ∑ i : Fin l, monomial i.val (A v t i : ℤ))
  have hw (i : Fin l) := f5_guard P g (Z.coeff i.val) _ (hd i) hg.1
  simp only [hw] at hr
  refine ⟨_, F5Encoding.encodes_integer_BTNContract_of_entries P l G T A hT, ?_⟩
  obtain ⟨time,final,htr,hhalt,htape,ht,hsp⟩ := hr
  have hKK : K ≤ K' := Nat.le_mul_of_pos_right _ (by positivity)
  have hp : polyBound K (S+desc.length) ≤ polyBound K' (S+desc.length) := by
    unfold polyBound
    apply mul_le_mul (by exact_mod_cast hKK) (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (S+desc.length)]) hKK) (by positivity) (by positivity)
  refine ⟨time,final,htr,hhalt,htape,ht.trans ?_,fun k c hk htr => (hsp k c hk htr).trans hp⟩
  exact mul_le_mul hp (f5_time K C b m hC hb hm hbm) (by positivity) (by unfold polyBound; positivity)
